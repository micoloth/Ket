
# [I'm afraid, first order] unification- Screw it, I'm going first order

# from https://github.com/jozefg/higher-order-unification/


# IMPORTANT idea on how to code CONTINUATIONS: And what types/constructions must be involved:
# IF you have a f:A->B function, you (can) ALSO have such a function: fc:C->B, where C stands for "CONFIRMATION/CONTINUATION",
# and where Such a function is GENERATED like this: if C(confirmation) is just a Constant that confirms a CANDIDATE a,
# fc={a.b}, where you CAN, OR NOT, precompute a.b.
# Otherwise, if a DEPENDS (in some known way ca:C->A ofc) from a param c,
# fc={x.ca.ab}, where you can STILL precompose ca.ab, and it MIGTH still be useful if ca STILL has some "pieces-of-a-like" internal state !!
# Really, the only problem is tho: That before you had a B, now you have C->B !!! Or at most, a (B + C->B) ....
# And so here we return to our favourite problems: IS THERE a match<> from (B + C->B) to B ?  How/when do/can you convert from B to 1->B and/or viceversa?
# What is the meaning of the "NTHG" function ????


# TGlob   TGlobTag
# TLoc   TLocTag
# TTop   TTopTag
# TTerm   TTermTag
# TAbs   TAbsTag
# TProd   TProdTag
# TSum   TSumTag
# TApp   TAppTag
# TSumTermTag   TSumTermTag
# TAnno   TAnnoTag
# TBranches   TBranchesTag

include("mylambda1_tag.jl")


abstract type Constraint end
struct DirectConstraint <: Constraint # (->)
    t1::TermTag
    t2::TermTag
end
struct ReverseConstraint <: Constraint# (Meaning <-)
    t1::TermTag
    t2::TermTag
end
struct EqConstraint <: Constraint # Should be equal.
    t1::TLocTag
    t2::TermTag
end
struct ErrorConstraint <: Constraint
    c::Constraint
    error::Error
end
Base.:(==)(a::EqConstraint, b::EqConstraint) = (a.t1 == b.t1) && (a.t2 == b.t2)
Base.:(==)(a::DirectConstraint, b::DirectConstraint) = (a.t1 == b.t1) && (a.t2 == b.t2)
Base.:(==)(a::ReverseConstraint, b::ReverseConstraint) = (a.t1 == b.t1) && (a.t2 == b.t2)
reduc(c::DirectConstraint) = DirectConstraint(reduc(c.t1), reduc(c.t2))
reduc(c::ReverseConstraint) = ReverseConstraint(reduc(c.t1), reduc(c.t2))
reduc(c::EqConstraint) = EqConstraint(reduc(c.t1), reduc(c.t2))
reduc(c::ErrorConstraint) = ErrorConstraint(reduc(c.c), c.error)


get_string(a::Array{ErrorConstraint}) = a .|> (x->"Can't unify $(x.c.t1 |>pr) and $(x.c.t2 |>pr): $(x.error)") |> (x->join(x, ", "))

Error = String
Imply_res = Union{Array{Constraint}, ErrorConstraint}

pr(c::Constraint)::String = pr(c.t1) * "==" * pr(c.t2)


#a join b  ==  a v b  ==  a<avb, b<avb  ==  a CAN BECOME a join b, b CAN BECOME a join b

struct MeetJoin_rec_res
    res_type::TermTag # OR would be better if each one had its own?  --> NOTE: maybe i can still template it?
    cs::Array{EqConstraint}
end

err_msg_app(t1::TAppTag, t2::TAppTag) = "Different bodies: $(length(t1.ops_dot_ordered)) != $(length(t2.ops_dot_ordered))"
err_msg_lambdas(t1::TAbsTag, t2::TAbsTag) = "Different lambdas $(pr(t1)) != $(pr(t2)): I know I'm being picky, but impossible to tell if these are the same: $([t1.body, t2.body])"
err_msg_sumtags(t1::TSumTermTag, t2::TSumTermTag) = "For now, you can NEVER unify different tags: $(t1.tag_name) != $(t2.tag_name)"
err_msg_terms(t1::TermTag, t2::TermTag) = "Different: $(pr(t1)) is really different from $(pr(t2))"
err_msg_prods(t1::TProdTag, t2::TProdTag) = "Different lengths: $(length(t1.data)) < $(length(t2.data)), so you cannot even drop."
err_msg_sums(t1::TSumTag, t2::TSumTag) = "Different lengths: $(length(t1.data)) > $(length(t2.data)), so if you are in the last case you are screwed.."

function meetjoin_rec_unify_(t1::TAppTag, t2::TAppTag, do_meet::Bool)::MeetJoin_rec_res
    if length(t1.ops_dot_ordered) != length(t2.ops_dot_ordered)
        return MeetJoin_rec_res(TermTagwError(t1, Error(err_msg_app(t1, t2))), Array{EqConstraint}[])
    end
    all_ress = [meetjoin_rec_unify_(f1, f2, do_meet) for (f1, f2) in zip(t1.ops_dot_ordered, t2.ops_dot_ordered)]
    MeetJoin_rec_res(TAppTag(all_ress .|> x->x.res_type), vcat((all_ress .|> x->x.cs)...))
end

function meetjoin_rec_unify_(t1::TProdTag, t2::TProdTag, do_meet::Bool)::MeetJoin_rec_res
    t1l, t2l = t1.data|>length, t2.data|>length
    all_ress = [meetjoin_rec_unify_(f1, f2, do_meet) for (f1, f2) in zip(t1.data, t2.data)] # Potentially turn into a monad (not really urgent tho)
    res_types = all_ress .|> x->x.res_type
    if t1l != t2l && do_meet
        additional_elems = (t1l>t2l) ? (t1.data[(t2l+1):end]) : (t2.data[(t1l+1):end])
        res_types = vcat(res_types, additional_elems)
    end
    MeetJoin_rec_res(TProdTag(Array{TermTag}(res_types)), vcat((all_ress .|> x->x.cs)...))
end

function meetjoin_rec_unify_(t1::TSumTag, t2::TSumTag, do_meet)::MeetJoin_rec_res
    all_ress = [meetjoin_rec_unify_(f1, f2, do_meet) for (f1, f2) in zip(t1.data, t2.data)] # Potentially turn into a monad (not really urgent tho)
    res_types = all_ress .|> x->x.res_type
    errors = findall((x->x isa TermTagwError), res_types)
    t1l, t2l = t1.data|>length, t2.data|>length
    if t1l != t2l && !do_meet
        additional_elems = (t1l>t2l) ? (t1.data[(t2l+1):end]) : (t2.data[(t1l+1):end])
        res_types = vcat(res_types, additional_elems)
    end
    res_type = TSumTag(res_type)
    if length(errors) > 0 res_type = TermTagwError(res_type, "E"*join(errors .|> string, "")) end
    MeetJoin_rec_res(res_type, vcat((all_ress .|> x->x.cs)...))
end


function meetjoin_rec_unify_(t1::TAbsTag, t2::TAbsTag, do_meet)::MeetJoin_rec_res
    println("Simplyfing two Foralls:")
    # FOR NOW, these will be REALLY PICKY
    if t1 == t2
        MeetJoin_rec_res(t1, Array{EqConstraint}[])
    else
        MeetJoin_rec_res(TermTagwError(t1, Error(err_msg_lambdas(t1, t2))), Array{EqConstraint}[])
    end
end

function meetjoin_rec_unify_(t1::TTermTag, t2::TTermTag, do_meet)::MeetJoin_rec_res
    res_out = meetjoin_rec_unify_(t1.t_out, t2.t_out, do_meet)
    res_in = meetjoin_rec_unify_(t1.t_in, t2.t_in, !do_meet)
    MeetJoin_rec_res(TTermTag(res_in.res_type, res_out.res_type), vcat(res_out.cs, res_in.cs))
end

function meetjoin_rec_unify_(t1::TSumTermTag, t2::TSumTermTag, do_meet)::MeetJoin_rec_res
    if t1.tag != t2.tag
        return MeetJoin_rec_res(TermTagwError(t1, Error(err_msg_sumtags(t1, t2))), Array{EqConstraint}[])
        # ^ You MIGHT want to return constraints for t1 and t2 all the same, but i'm NOT doing it...
    else
        res = meetjoin_rec_unify_(t1.data, t2.data, do_meet) # Wait.... Is this even right? How does a type-level sum play with type-level Locs ???
        return MeetJoin_rec_res(TSumTermTag(t1.tag, t1.tag_name, res.res_type), res.cs)
    end
end
function meetjoin_rec_unify_(t1::TermTag, t2::TSumTermTag, do_meet)::MeetJoin_rec_res
    # This behaviour is pretty weird admiddetly, and it simply says: SCREW TAG, essentially
    if (t1 isa TLocTag) MeetJoin_rec_res(t1, Array{EqConstraint}([EqConstraint(t1, t2)]))
    else
        res = meetjoin_rec_unify_(t1, t2.data, do_meet) # Wait.... Is this even right? How does a type-level sum play with type-level Locs ???
        MeetJoin_rec_res(TSumTermTag(t2.tag, t1.tag_name, res.res_type), res.cs)
    end
end
function meetjoin_rec_unify_(t1::TSumTermTag, t2::TermTag, do_meet)::MeetJoin_rec_res
    # This behaviour is pretty weird admiddetly, and it simply says: SCREW TAG, essentially
    if (t2 isa TLocTag) MeetJoin_rec_res(t2, Array{EqConstraint}([EqConstraint(t2, t1)]))
    else
        res = meetjoin_rec_unify_(t1.data, t2, do_meet) # Wait.... Is this even right? How does a type-level sum play with type-level Locs ???
        MeetJoin_rec_res(TSumTermTag(t1.tag, t1.tag_name, res.res_type), res.cs)
    end
end

function meetjoin_rec_unify_(t1::TLocTag, t2::TLocTag, do_meet)::MeetJoin_rec_res
    if t1.var_tag == t2.var_tag # t1.var == t2.var
        MeetJoin_rec_res(t2, Array{EqConstraint}([]))
    else
        MeetJoin_rec_res(t2, Array{EqConstraint}([EqConstraint(t1, t2)]))
    end
end

function meetjoin_rec_unify_(t1::TermTag, t2::TermTag, do_meet)::MeetJoin_rec_res # base case
    if t1 == t2 MeetJoin_rec_res(t1, Array{EqConstraint}([]))
    elseif t1 isa TLocTag MeetJoin_rec_res(t1, Array{EqConstraint}([EqConstraint(t1, t2)]))
    elseif t2 isa TLocTag MeetJoin_rec_res(t2, Array{EqConstraint}([EqConstraint(t2, t1)]))
    else MeetJoin_rec_res(TermTagwError(t1, Error(err_msg_terms(t1, t2))), Array{EqConstraint}[])
    end
end

function imply_unify_(t1::TAppTag, t2::TAppTag)::Imply_res
    if length(t1.ops_dot_ordered) != length(t2.ops_dot_ordered)
        ErrorConstraint(DirectConstraint(t1, t2), Error(err_msg_app(t1, t2)))
    else
        Array{Constraint}([DirectConstraint(s1, s2) for (s1, s2) in zip(t1.ops_dot_ordered, t2.ops_dot_ordered)])
    end
end

function imply_unify_(t1::TProdTag, t2::TProdTag)::Imply_res
    if length(t1.data) < length(t2.data) ErrorConstraint(DirectConstraint(t1, t2), Error(err_msg_prods(t1, t2)))
    else Array{Constraint}([DirectConstraint(s1, s2) for (s1, s2) in zip(t1.data, t2.data)])
    end
    # union([imply_unify_(s1, s2) for (s1, s2) in zip(args1, args2)]...)
    # union((zip(args1, args2) .|> ((a1, a2),)->imply_unify_(a1, a2))...)
    # Array{Constraint}([DirectConstraint(s1, s2) for (s1, s2) in zip(args1.data, args2.data)])
end

function imply_unify_(t1::TAbsTag, t2::TAbsTag)::Imply_res
    println("Simplyfing two Foralls:")
    # FOR NOW, these will be REALLY PICKY
    if t1 == t2 Array{Constraint}([])
    else ErrorConstraint(DirectConstraint(t1, t2), Error(err_msg_lambdas(t1, t2)))
    end
    # Only accepted case: All constraints are about TLocTag only and THE SAME
    # cons = DirectConstraint(t1.body, t2.body)
    # cons = simplify(cons)
    # is_same(c::Constraint) = (c.t1 isa TLocTag) && (c.t1 == c.t2)
    # if typeof(cons) == Error
    #     Error("Different lambdas: with this error: $(cons)")
    # elseif length(cons) == 0 || (cons .|> is_same |> all)
    #     Array{Constraint}([])
    # else
    #     Error("Different lambdas $(pr(t1)) != $(pr(t2)): I know I'm being picky, but impossible to simplify this part: $(cons)")
    # end
end

function imply_unify_(t1::TTermTag, t2::TTermTag)::Imply_res
    Array{Constraint}([
        DirectConstraint(t1.t_out, t2.t_out),
        ReverseConstraint(t1.t_in, t2.t_in)])
end

function imply_unify_(t1::TLocTag, t2::TLocTag)::Imply_res
    Array{Constraint}([DirectConstraint(t1, t2)])
end

function imply_unify_(t1::TSumTag, t2::TSumTag)::Imply_res
    if length(t1.data) > length(t2.data) ErrorConstraint(DirectConstraint(t1, t2), Error(err_msg_sums(t1, t2)))
    else Array{Constraint}([DirectConstraint(s1, s2) for (s1, s2) in zip(t1.data, t2.data)])
    end
end

function imply_unify_(t1::TSumTermTag, t2::TSumTermTag)::Imply_res
    if t1.tag != t2.tag ErrorConstraint(DirectConstraint(t1, t2), Error(err_msg_sumtags(t1, t2)))
    else Array{Constraint}([DirectConstraint(t1.data, t2.data)])
    end
end
function imply_unify_(t1::TermTag, t2::TSumTermTag)::Imply_res
    # This behaviour is pretty weird admiddetly, and it simply says: SCREW TAG, essentially
    if (t1 isa TLocTag) Array{Constraint}([DirectConstraint(t1, t2)])
    else Array{Constraint}([DirectConstraint(t1, t2.data)])
    end
end
function imply_unify_(t1::TSumTermTag, t2::TermTag)::Imply_res
    # This behaviour is pretty weird admiddetly, and it simply says: SCREW TAG, essentially
    if (t2 isa TLocTag) Array{Constraint}([DirectConstraint(t1, t2)])
    else Array{Constraint}([DirectConstraint(t1.data, t2)])
    end
end
function imply_unify_(t1::TermTag, t2::TermTag)::Imply_res # base case
    if t1 == t2 Array{Constraint}([])
    elseif typeof(t1) === TLocTag || typeof(t2) === TLocTag Array{Constraint}([DirectConstraint(t1, t2)])
    else ErrorConstraint(DirectConstraint(t1, t2), Error(err_msg_terms(t1, t2)))
    end
end

swap(c::DirectConstraint) = ReverseConstraint(c.t2, c.t1)
swap(c::ReverseConstraint) = DirectConstraint(c.t2, c.t1)
swap(c::ErrorConstraint) = ErrorConstraint(swap(c.c), c.error)
imply_unify_(c::DirectConstraint)::Imply_res = imply_unify_(c.t1, c.t2)
function imply_unify_(c::ReverseConstraint)::Imply_res
    res = imply_unify_(c.t2, c.t1)
    (res isa ErrorConstraint) ? (res |> swap) : Array{Constraint}(res .|> swap)
end









# Unify: solve f(x) = g(y) in the sense of finding x AND y,
# EXCEPT it WONT fail if post-applying some DROPPINGs here and there will help.
# It WONT RETURN THEM, either. See above.

# idea: in NO CASE x=f(x) can be solved, (if types_ are REDUCED), because we handle RecursiveTypes Differently!!
function check_not_recursive(tloc::TLocTag, tt::TermTag)::Bool
    for v in usesLocsSet(tt) # THIS IS DIFFERENT IN VAR VS VAR_TAG
    if tloc.var_tag == v return false end # THIS IS DIFFERENT IN VAR VS VAR_TAG
    end
    return true
end

get_reduc_subst(t::Array{TProdTag}) = TAppTag(vcat([t[end]], t[end - 1:-1:1] .|> (x -> TAbsTag(x))))
get_reduc_subst(t::Array{TermTag}) = TAppTag(vcat([t[end]], t[end - 1:-1:1] .|> (x -> TAbsTag(x))))
# IMPORTANT: ALL EXCEPT (potentially) the >FIRST< should be TPRODS !!!!!

# ASSOCIATIVE OPERATION to compose the above:
ass_smart_reduc(t...) = (length(t) <= 1) ? (collect(t)) : ([get_reduc_subst(collect(t)) |> reduc])
# TODO: change "[reduc()]" in "smart_reduc" !!
ass_reduc(t::TProdTag ...)::TProdTag = (length(t) == 1) ? (t[1]) : (get_reduc_subst(collect(t)) |> reduc)
ass_reduc(t1::TermTag, ts::TProdTag ...)::TermTag = (length(ts) == 0) ? (t1) : (get_reduc_subst(vcat([t1], collect(ts))) |> reduc)

ass_reduc(c::EqConstraint, ts::TProdTag ...) = EqConstraint(ass_reduc(c.t1, ts...), ass_reduc(c.t2, ts...))
ass_reduc(c::DirectConstraint, ts::TProdTag ...) = DirectConstraint(ass_reduc(c.t1, ts...), ass_reduc(c.t2, ts...))
ass_reduc(c::ReverseConstraint, ts::TProdTag ...) = ReverseConstraint(ass_reduc(c.t1, ts...), ass_reduc(c.t2, ts...))
ass_reduc(c::ErrorConstraint, ts::TProdTag ...) = ErrorConstraint(ass_reduc(c.c, ts...), c.error)

function get_subst_prod_OLD(tloc::TLocTag, tt::TermTag, current_arity)::TProdTag
    # resulting_arity = current_arity - 1
    # you have ALREADY TESTED that tt does not contain tloc, that's the whole point !!!!
    prod = vcat(
        Array{TermTag}([TLocTag(i) for i in 1:(tloc.var - 1)]),
        Array{TermTag}([TLocTag(0)]), # Placeholder, complete nonsense, it's getting replaced
        Array{TermTag}([TLocTag(i) for i in (tloc.var:current_arity - 1)])
    )
    prod[tloc.var] = ass_reduc(tt, TProdTag(prod))
    TProdTag(prod)
end  # THIS IS DIFFERENT IN VAR VS VAR_TAG # TODOTODOTODOTODO
function get_subst_prod(tloc::TLocTag, tt::TermTag, current_arity)::TProdTag
    # resulting_arity = current_arity - 1
    # you have ALREADY TESTED that tt does not contain tloc, that's the whole point !!!!
    prod = TProdTag(Array{TermTag}([TLocTag(i) for i in current_arity]), Array{String}([current_arity...]))
    pos_tt = findfirst(x->x==tloc.var_tag, prod.tags)[1]
    prod.data[pos_tt] = ass_reduc(tt, prod)
    prod
end  # THIS IS DIFFERENT IN VAR VS VAR_TAG # TODOTODOTODOTODO


# function share_ctx_tlocs_names(t1::TAbsTag, t2::TAbsTag, t1arity::Index, t2arity::Index)
#     s1 = TProdTag(Array{TermTag}([TLocTag(i) for i in 1:t1arity]))
#     s2 = TProdTag(Array{TermTag}([TLocTag(i) for i in (t1arity + 1):(t1arity + t2arity)]))
#     TAppTag([s1, t1]), TAppTag([s2, t2])
# end
# function share_ctx_tlocs_names_get_substs(t1arity::Index, t2arity::Index)
#     s1 = TProdTag(Array{TermTag}([TLocTag(i) for i in 1:t1arity]))
#     s2 = TProdTag(Array{TermTag}([TLocTag(i) for i in (t1arity + 1):(t1arity + t2arity)]))
#     s1, s2
# end

struct ItsLiterallyAlreadyOk end

function get_first_pair_of_matching_indices(v::Array{Id}) # TODOTODOTODOTODO This changed !!!
    for i in 1:length(v)
        for j in i+1:length(v)
            if v[i] == v[j] return (i,j) end
        end
    end
    nothing
end
function get_loc_loc_constraint(v)
    for i in 1:length(v)
        if !(v[i] isa ErrorConstraint) && (v[i].t1 isa TLocTag && v[i].t2 isa TLocTag) return i end
    end
    nothing
end

@enum Unify_mode meet_=1 join_=2 imply_=3
Succeded_unif_res = Tuple{TProdTag, TProdTag, TermTag}
Failed_unif_res = Tuple{TProdTag, TProdTag, TermTag, Array{ErrorConstraint}}

function robinsonUnify(t1::TAbsTag, t2::TAbsTag, t1arity, t2arity; unify_tlocs_ctx::Bool = true, mode::Unify_mode=join_)::Union{Succeded_unif_res, Failed_unif_res, ItsLiterallyAlreadyOk}
    there_are_errors::Bool = false

    # 1. Share TLocs
    # if unify_tlocs_ctx # THIS IS DIFFERENT IN VAR VS VAR_TAG # IS IT ENOUGH TO NOT DO THIS ???? # TODOTODOTODOTODO
    #     current_arity = t1arity + t2arity
    #     t1, t2 = share_ctx_tlocs_names(t1, t2, t1arity, t2arity)
    # else
    #     # This means Sharing of names has ALREADY HAPPENED !!!
    #     current_arity = max(t1arity, t2arity)
    #     t1, t2 = t1.body, t2.body
    # end

    current_arity = union(t1arity, t2arity)
    t1, t2 = t1.body, t2.body

    # 2. unify term and/or produce Eqconstraints
    if mode==imply_
        STACK = Array{Constraint}([DirectConstraint(t1, t2)])
        ERRORSTACK = Array{ErrorConstraint}([])
    else
        t1, t2 = reduc(t1), reduc(t2)
        res = meetjoin_rec_unify_(t1, t2, mode==meet_)
        res_type::TermTag, STACK = res.res_type, res.cs
        # NOTE: meetjoin_rec_unify_ DOESNT return ErrorConstraint's, at worst it returns TermTagwError's
        if has_errors(res_type) there_are_errors = true end
        ERRORSTACK = Array{ErrorConstraint}([])
    end

    # 3. Solve all constraints:
    current_total_subst = Array{TProdTag}([]) # SMART_REDUCED VERSION # (Can be a single [TProdTag] or the whole list)
    # ^ Still, to pass into get_reduc_subst IN THIS ORDER

    # 3.1 Remove all loc-loc constraint first
    while (i=get_loc_loc_constraint(STACK)) !== nothing
        l1, l2 = parse(Int, STACK[i].t1.var_tag), parse(Int, STACK[i].t2.var_tag)
        # ^ it WILL break if these are not Ints, which is Exactly what i want. There should be no such constraints between strings.
        deleteat!(STACK, i)
        if l1 == l2 continue end # cannot hurt can it?
        var, tt = max(l1, l2), TLocTag(min(l1, l2))
        new_subst = get_subst_prod(TLocTag(var), tt, current_arity)
        current_total_subst = Array{TProdTag}(ass_smart_reduc(current_total_subst..., new_subst))
        current_arity = usedLocsSet(current_total_subst[end]) # The beauty of this is this is Enough... I HOPE LOL
        for i in 1:length(STACK)
            STACK[i] = ass_reduc(STACK[i], new_subst)
            # ^ Really, this is the EASY way:
            # EACH Constraint GETS >ALL< SUBSTS, ONE BY ONE, FROM THE MOMENT IT ENTERS THE STACK ONWARD.
            # A Better way would be: TRACK When each Contraint enters the stack. When you Consider that contraint,
            # apply to it the PREASSOCIATED CURRENT_TOTAL_SUBST of the substs it missed After it was created !!!
            # (wait.. That doesnt sound easy, as that means you can NEVER preassociate anything ?)
        end
        for i in 1:length(ERRORSTACK) ERRORSTACK[i] = ass_reduc(ERRORSTACK[i], new_subst) end
    end

    # 3.2 This while loop is Important for Meeting, while it can be Skipped for directional case
    # POSSIBLE OPTIMIZATION: Keep the TLocs in STACK Sorted, or even in a Dict ofc
    if mode != imply_
        while (ij = get_first_pair_of_matching_indices(STACK.|> (x->x.t1.var_tag))) !== nothing  #TODOTODOTODOTODO changed !!  get_first_pair_of_matching_indices too !
            tloc, ct1, ct2 = STACK[ij[1]].t1, STACK[ij[1]].t2, STACK[ij[2]].t2
            deleteat!(STACK, ij[2])
            deleteat!(STACK, ij[1])
            if !check_not_recursive(tloc, ct1) push!(ERRORSTACK, ErrorConstraint(EqConstraint(tloc, ct1), Error("$(tloc) == $(ct1) is not a thing (recursive)"))); continue end
            if !check_not_recursive(tloc, ct2) push!(ERRORSTACK, ErrorConstraint(EqConstraint(tloc, ct2), Error("$(tloc) == $(ct2) is not a thing (recursive)"))); continue end
            res = meetjoin_rec_unify_(ct1, ct2, mode==meet_)
            # Wait.. Are you COMPLETELY SURE you NEVER want a !MODE here ??? ??? ??? ???
            if has_errors(res_type) there_are_errors = true end
            push!(STACK, EqConstraint(tloc, res.res_type))
            if res.res_type isa TermTagwError there_are_errors = true # TODO: wtf?? I'm missing smthg here .... Where does it go?
            else
                append!(STACK, res.cs)
            end
        end
    end

    # 3.3 Substitute away all the constrains, one by one
    while (length(STACK) > 0)
        c = pop!(STACK)
        ct1, ct2 = c.t1, c.t2
        if !(ct1 isa TLocTag || ct2 isa TLocTag)
            @assert mode == imply_
            cs_inside = imply_unify_(reduc(c))
            if cs_inside isa ErrorConstraint push!(ERRORSTACK, cs_inside)
            else append!(STACK, cs_inside) end
            continue
        elseif ct1 isa TLocTag && ct2 isa TLocTag
            # NOTE: it would be NICE if i reworked Imply_ mode so that this DOESNT happen ... println("Does locloc Still happen? Ever ????? (Here, w/ $(ct1) and $(ct2))")
            if ct1.var_tag == ct2.var_tag continue end # cannot hurt can it?
            throw(DomainError("This never happens.. Right.. Right?? $(ct1) required to be $(ct2)"))
            var, tt = ct1.var, ct2 # it's ARBITRARY since these names have no meaning anyway
        elseif ct1 isa TLocTag
            if !check_not_recursive(ct1, ct2) push!(ERRORSTACK, ErrorConstraint(EqConstraint(ct1, ct2), Error("$(ct1) == $(ct2) is not a thing (recursive)"))); continue end
            var, tt = ct1.var, ct2
        elseif ct2 isa TLocTag
            if !check_not_recursive(ct2, ct1) push!(ERRORSTACK, ErrorConstraint(EqConstraint(ct2, ct1), Error("$(ct2) == $(ct1) is not a thing (recursive)"))); continue end
            var, tt = ct2.var, ct1
        end
        new_subst = get_subst_prod(TLocTag(var), tt, current_arity)
        current_total_subst = Array{TProdTag}(ass_smart_reduc(current_total_subst..., new_subst))
        current_arity = usedLocsSet(current_total_subst[end]) # The beauty of this is this is Enough... I HOPE LOL
        for i in 1:length(STACK)
            STACK[i] = ass_reduc(STACK[i], new_subst)
            # ^ Really, this is the EASY way:
            # EACH EqConstraint GETS >ALL< SUBSTS, ONE BY ONE, FROM THE MOMENT IT ENTERS THE STACK ONWARD.
            # A Better way would be: TRACK When each Contraint enters the stack. When you Consider that contraint,
            # apply to it the PREASSOCIATED CURRENT_TOTAL_SUBST of the substs it missed After it was created !!!
            # (wait.. That doesnt sound easy, as that means you can NEVER preassociate anything ?)
        end
        for i in 1:length(ERRORSTACK) ERRORSTACK[i] = ass_reduc(ERRORSTACK[i], new_subst) end
    end

    if length(current_total_subst) == 0 && !there_are_errors && length(ERRORSTACK) ==0
        return ItsLiterallyAlreadyOk()
    elseif length(current_total_subst) == 0
        res_type = if (mode == imply_) TGlobTag("O") else res_type end
        return Failed_unif_res([TProdTag(Array{TermTag}([])), TProdTag(Array{TermTag}([])), res_type, ERRORSTACK])
    end
    final_subst = ass_reduc(current_total_subst...)
    # subst1 = TProdTag(final_subst.data[1:t1arity])
    # subst2 = if unify_tlocs_ctx TProdTag(final_subst.data[(t1arity + 1):(t1arity + t2arity)]) else subst2 = TProdTag(final_subst.data[1:t2arity]) end
    subst1, subst2 = final_subst, final_subst
    res_type = if (mode == imply_) TGlobTag("O") # Why nothing: USE >>t2<< ( The Original one, NOT the Shared version)
    else ass_reduc(res_type, final_subst) end

    if there_are_errors || length(ERRORSTACK) > 0
        return Failed_unif_res([subst1, subst2, res_type, ERRORSTACK])
    else return Succeded_unif_res([subst1, subst2, res_type])
    end
end

# The following handles ALL THE CONFUSION ARISING FROM having or not having the Forall() at random.
robinsonUnify(t1::TAbsTag, t2::TermTag, t1arity, t2arity; unify_tlocs_ctx::Bool = true, mode::Unify_mode=join_) = robinsonUnify(t1, TAbsTag(t2), t1arity, t2arity; unify_tlocs_ctx=unify_tlocs_ctx, mode=mode)
robinsonUnify(t1::TermTag, t2::TAbsTag, t1arity, t2arity; unify_tlocs_ctx::Bool = true, mode::Unify_mode=join_) = robinsonUnify(TAbsTag(t1), t2, t1arity, t2arity; unify_tlocs_ctx=unify_tlocs_ctx, mode=mode)
function robinsonUnify(t1::TermTag, t2::TermTag, t1arity, t2arity; unify_tlocs_ctx::Bool = true, mode::Unify_mode=join_)
    if (t1arity == 0) && (t2arity == 0)
        return true #(t1 == t2) ? (TProdTag([]), TProdTag([])) : Error(" Not unifiable: $(t1) != $(t2)")
    else
        return robinsonUnify(TAbsTag(t1), TAbsTag(t2), t1arity, t2arity; unify_tlocs_ctx=unify_tlocs_ctx, mode=mode)
    end
end


# All cases WITHOUT precomputed tarities:
robinsonUnify(t1::TAbsTag, t2::TAbsTag; unify_tlocs_ctx::Bool = true, mode::Unify_mode=join_) = robinsonUnify(t1, t2, t1.body |> usedLocsSet, t2.body |> usedLocsSet; unify_tlocs_ctx=unify_tlocs_ctx, mode=mode)
robinsonUnify(t1::TAbsTag, t2::TermTag; unify_tlocs_ctx::Bool = true, mode::Unify_mode=join_) = robinsonUnify(t1, TAbsTag(t2), t1.body |> usedLocsSet, t2 |> usedLocsSet; unify_tlocs_ctx=unify_tlocs_ctx, mode=mode)
robinsonUnify(t1::TermTag, t2::TAbsTag; unify_tlocs_ctx::Bool = true, mode::Unify_mode=join_) = robinsonUnify(TAbsTag(t1), t2, t1 |> usedLocsSet, t2.body |> usedLocsSet; unify_tlocs_ctx=unify_tlocs_ctx, mode=mode)
robinsonUnify(t1::TermTag, t2::TermTag; unify_tlocs_ctx::Bool = true, mode::Unify_mode=join_) = robinsonUnify(TAbsTag(t1), TAbsTag(t2), t1 |> usedLocsSet, t2 |> usedLocsSet; unify_tlocs_ctx=unify_tlocs_ctx, mode=mode)




# Type inference

# IMPORTANT: I'm using TTermTag's for carrying around contexts, but PLEASE make sure it's always TTermTag OF A TPROD...

TTermEmpty(res_type::TermTag) = TTermTag(TProdTag(Array{TermTag}([])), res_type)

function infer_type_(term::TLocTag)::TermTag
    s = tryparse(Int, term.var_tag)
    if s !== nothing
        return TTermTag(TProdTag(Array{TermTag}([term])), term)  # TAbsTag(TLocTag(term.var)) was an idea i tried
    else
        return TTermTag(TProdTag(Array{TermTag}([TLocTag(i) for i in 1:term.var])), TLocTag(term.var))  # TAbsTag(TLocTag(term.var)) was an idea i tried
    end
end # TODOTODOTODO (but also kinda this is right)
function infer_type_(term::TGlobTag)::TermTag
    if term.type isa TAbsTag return TTermEmpty(term.type.body)
    # ^ This is because TTermTag's are Naked (no Forall) for some reason- BOY will this become a mess
    else return TTermEmpty(term.type) end
end
function infer_type_(term::TTopTag)::TermTag return TTermEmpty(TTopTag()) end
function infer_type_(term::TAnnoTag, t_computed::TTermTag)::TermTag # IMPORTANT: if an error comes up, THIS FUNCTION will turn res into TermTagwError
    substs = robinsonUnify(t_computed.t_out, term.type, mode=imply_)
    if substs isa ItsLiterallyAlreadyOk return TTermTag(t_computed.t_in, term.type) end
    term_type = if term.type isa TAbsTag term.type.body else term.type end   # Oh fuck what am i doing
    args = if (t_computed.t_in.data |> length == 0) TProdTag(Array{TermTag}([])) else ass_reduc(t_computed.t_in, substs[1]) end  # HOPEFULLY this is a Type, NOT a body
    res = TTermTag(args, ass_reduc(term_type, substs[2]))
    if substs isa Failed_unif_res res = TermTagwError(res, Error("Wrong annotation: " * get_string(subst[4]))) end
    # NOTE^ :  mode=imply_ doesnt even return a res_type, even less one with an error! Of course
    res
end

function infer_type_(term::TProdTag, ts_computed::Array{TTermTag})::TermTag # IMPORTANT: if an error comes up, THIS FUNCTION will turn res into TermTagwError
    # IDEA: This checking that all args are the same, really belongs to the DIAGONAL FUNCTOR of terms,
    # but this is a hodgepodge, so that's fine.
    # @assert length(term.data) == length(ts_computed) "$(length(term.data)) != $(length(ts_computed)) in $(term.data) != $(ts_computed)"
    # ^ i REALLY WANT to have this, except that HORRIBLE HACK in infer(TAppTag) passes an EMPTY EPROD here...

    # IDEA: if max_eargs_length == 0, you STILL have to UNIFY the TLocs, which is currenty done by
    # JUST RUNNING robinsonUnify on the Empty prods, and using that behaviour.
    unified_RES_types::Array{TermTag} = Array{TermTag}([ts_computed[1].t_out])
    args, full_arity = ts_computed[1].t_in, ts_computed[1] |> usedLocsSet
    all_errors = Array{ErrorConstraint}([])
    for t in ts_computed[2:end]
        # s1, s2 = share_ctx_tlocs_names_get_substs(full_arity, t |> usedLocsSet)
        # args, t = ass_reduc(args, s1), ass_reduc(t, s2)
        # unified_RES_types = unified_RES_types .|> (x -> ass_reduc(x, s1))
        # TODOTODOTODO # Not sharing vars
        full_arity = union(args|>usedLocsSet, t|>usedLocsSet)
        res = robinsonUnify(
            TAbsTag(args), TAbsTag(t.t_in), full_arity, full_arity;
            unify_tlocs_ctx=false, mode=meet_)
        # if res isa Failed_unif_res
        #     return Error("ELocs typed $(t.arg_types .|> pr) cannot be unified into ELocs typed $(args.arg_types .|> pr), with error '$(res)'")
        if res isa ItsLiterallyAlreadyOk
            push!(unified_RES_types, t.t_out)
            full_arity = union(args|>usedLocsSet, t|>usedLocsSet)
            continue
        end
        if res isa Failed_unif_res
            s1, s2, meeted, errors = res
            append!(all_errors, errors)
            # TODO: if has_errors(meeted) # Dunno what to do :(
        else
            s1, s2, meeted = res
        end
        args = meeted
        unified_RES_types = unified_RES_types .|> (x -> ass_reduc(x, s1)) # if they BECAME EQUAL to the stuff "args" comes from, this should work.. No?
        push!(unified_RES_types, ass_reduc(t.t_out, s2))
        full_arity = union(s1|>usedLocsSet, s2|>usedLocsSet) # god i HOPE this makes sense.....
    end
    res = TTermTag(args, TProdTag(Array{TermTag}(unified_RES_types)))
    if length(all_errors) > 0 # Or there's some error into res !!
        res = TermTagwError(res, Error("Impossible to unify args of this prod: " * get_string(all_errors))) end
    res
end

function infer_type_(term::TAbsTag, t_computed::TTermTag)::TermTag
    return TTermTag(TProdTag(Array{TermTag}([])), t_computed)
end
function infer_type_(term::TSumTermTag, t_computed::TTermTag)::TermTag
    arT, tag = t_computed |> usedLocsSet, term.tag
    types = vcat([TLocTag(n) for n in (arT + 1):(arT + tag - 1)], [t_computed.t_out])
    return TTermTag(t_computed.t_in, TAbsTag(TSumTag(types)))
end
function infer_type_(term::TBranchesTag, t_computed::TTermTag)::TermTag
    arT, tag = t_computed |> usedLocsSet, term.tag
    types = vcat([TLocTag(n) for n in (arT + 1):(arT + tag - 1)], [t_computed.t_out])
    return TTermTag(t_computed.t_in, TAbsTag(TSumTag(types)))
end

function infer_type_(term::TAppTag, ts_computed::Array{TTermTag})::TermTag
    # First, fix TLocTag's by SQUASHING THEM TO BE TTERMS.
    # Idea: - TAbsTag come as TTErms (TTermTag with NO dependencies)  - ELocs come as InfRes WITH the dependency  - NONE of the TTermTag have a Forall around cuz it's how it is in this mess
    ts_computed_2 = Array{TTermTag}([ts_computed[1]])
    for t in ts_computed[2:end]
        fake_tterm = TAbsTag(TTermTag(TLocTag(1), TLocTag(2)))
        tterm_subst = robinsonUnify(t.t_out, fake_tterm, t |> usedLocsSet, fake_tterm.body |> usedLocsSet; mode=imply_)
        # NOTE^ :  mode=imply_ doesnt even return a res_type, even less one with an error! Of course
        if tterm_subst isa Failed_unif_res return TermTagwError(TAppTag(ts_computed.|>(x->x.t_out)), Error("Calling non function: " * get_string(tterm_subst[4]))) #y'know what? Yes this is violent.. I don't care
        elseif tterm_subst isa ItsLiterallyAlreadyOk push!(ts_computed_2, t)
        else push!(ts_computed_2, ass_reduc(t, tterm_subst[1])) # t.t_out SHOULD be nothing else but a TTermTag... RIGTH?
        end
    end
    # ^ Each of these still has ITS OWN TLocTag's

    # Second, Unify the context of the TLocs:
    all_w_unified_args = infer_type_(TProdTag(Array{TermTag}([])), ts_computed_2)
    # ^ REUSING the TProdTag inference, HACKING the fact that TermTag is NOT used
    # What comes out is a: TTermTag(TProdTag(Array{TermTag}([...])), TProdTag(Array{TermTag}(([TTermTag(), ...]))))
    full_arity = all_w_unified_args |> usedLocsSet
    # ^Can i compute this in some smarter way?  # Dunno !
    args, tterms = all_w_unified_args.t_in, all_w_unified_args.t_out.data
    # ^ ts_computed_out becomes array and args remains TProdTag.. What a mess
    all_errors = Array{ErrorConstraint}([])
    # Third, actually unify all in/outs:
    prev_out = tterms[1] # TODO fix when app is not a mess anymore
    for i in 2:length(tterms)
        next_in = tterms[i].t_in # YES this always exists now
        substs =  robinsonUnify(
            TAbsTag(prev_out), TAbsTag(next_in), full_arity, full_arity; unify_tlocs_ctx=false, mode=imply_)
        # TODO: i DONT LIKE these TAbsTag, it's WRONG, but, it's the only way of accessing unify_tlocs_ctx atm
        # NOTE^ :  mode=imply_ doesnt even return a res_type, even less one with an error! Of course
        if substs isa ItsLiterallyAlreadyOk
            prev_out = tterms[i].t_out
        else
            if substs isa Failed_unif_res append!(all_errors, substs[4]) end
            (s1, s2) = substs
            # ^ Wait.. Are you telling me, if unify_tlocs_ctx=false, s1 and s2 are ALWAYS the same ???  # # Man, this is a crazy world..
            tterms = ass_reduc(TProdTag(Array{TermTag}(tterms)), s1).data
            # ^ the LENGTH of tterms DOES NOT CHANGE HERE
            # ^ Also Maybe you can SKIP updating all of them but who cares
            args = ass_reduc(args, s1) # Keep track of the Arg types, too
            full_arity = s1 |> usedLocsSet
            prev_out = tterms[i].t_out
            # Error("Mismatched app: get out type $(prev_out |> pr) but required type $(next_in |> pr), with error '$()'")
        end
    end
    res = TTermTag(args, tterms[end].t_out)
    if length(all_errors) > 0 res = TermTagwError(res, Error("Type of the application don't match: " * get_string(all_errors))) end
    # Returns the OUTPUT type instead of the composed TTermTag type cuz this is a mess
    res
end



# Silly categorical-algebra-ish recursive wrapup:
function infer_type_rec(term::TLocTag)::TermTag return infer_type_(term) end
function infer_type_rec(term::TGlobTag)::TermTag return infer_type_(term) end
function infer_type_rec(term::TTopTag)::TermTag return infer_type_(term) end
function infer_type_rec(term::TAnnoTag)::TermTag # IMPORTANT: if an error comes up, THIS FUNCTION will turn res into TermTagwError
    tt = infer_type_rec(term.expr)
    # return (tt isa Error) ? tt : infer_type_(term, tt)
    return infer_type_(term, tt)
end
function infer_type_rec(term::TAbsTag)::TermTag  tt = infer_type_rec(term.body); return (tt isa Error) ? tt : infer_type_(term, tt) end
function infer_type_rec(term::TProdTag)::TermTag
    tts::Array{Union{TTermTag,Error} } = infer_type_rec.(term.data)
    # for tt in tts if tt isa Error return tt end end
    return infer_type_(term, Array{TTermTag}(tts))
end
function infer_type_rec(term::TSumTermTag)::TermTag  tt = infer_type_rec(term.data); return (tt isa Error) ? tt : infer_type_(term, tt) end
function infer_type_rec(term::TBranchesTag)::TermTag
    tts = infer_type_rec.(term.ops_chances)
    # for tt in tts if tt isa Error return tt end end
    return infer_type_(term, Array{TTermTag}(tts))
end
function infer_type_rec(term::TAppTag)::TermTag # IMPORTANT: if an error comes up, THIS FUNCTION will turn res into TermTagwError
    tts::Array{Union{TTermTag,Error}} = infer_type_rec.(term.ops_dot_ordered)
    # for tt in tts if tt isa Error return tt end end
    return infer_type_(term, Array{TTermTag}(tts))
end


# *unification*, thproving_1.jl, mylambda1_dep.jl