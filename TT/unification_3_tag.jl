
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
# TSumT   TSumTermTag
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
Base.:(==)(a::EqConstraint, b::EqConstraint) = (a.t1 == b.t1) && (a.t2 == b.t2)
Base.:(==)(a::DirectConstraint, b::DirectConstraint) = (a.t1 == b.t1) && (a.t2 == b.t2)
Base.:(==)(a::ReverseConstraint, b::ReverseConstraint) = (a.t1 == b.t1) && (a.t2 == b.t2)
reduc(c::DirectConstraint) = DirectConstraint(reduc(c.t1), reduc(c.t2))
reduc(c::ReverseConstraint) = ReverseConstraint(reduc(c.t1), reduc(c.t2))
reduc(c::EqConstraint) = EqConstraint(reduc(c.t1), reduc(c.t2))


Error = String
SimpRes = Union{Array{Constraint},Error}

pr(c::Constraint)::String = pr(c.t1) * "==" * pr(c.t2)


#a join b  ==  a v b  ==  a<avb, b<avb  ==  a CAN BECOME a join b, b CAN BECOME a join b

struct MeetJoin_rec_res
    res_type::TermTag # OR would be better if each one had its own?  --> NOTE: maybe i can still template it?
    cs::Array{EqConstraint}
end

err_msg_app(t1::TAppTag, t2::TAppTag) = "Different bodies: $(length(t1.ops_dot_ordered)) != $(length(t2.ops_dot_ordered))"
err_msg_lambdas(t1::TAbsTag, t2::TAbsTag) = "Different lambdas $(pr(t1)) != $(pr(t2)): I know I'm being picky, but impossible to tell if these are the same: $([t1.body, t2.body])"
err_msg_sumtags(t1::TSumTerm, t2::TSumTerm) = "For now, you can NEVER unify different tags: $(t1.tag_name) != $(t2.tag_name)"

function meetjoin_rec_unify_(t1::TAppTag, t2::TAppTag, do_meet::Bool)::MeetJoin_rec_res
    if length(t1.ops_dot_ordered) != length(t2.ops_dot_ordered)
        return TermTagwError(t1, Error(err_msg_app(t1, t2)))
    end
    all_ress = [meetjoin_rec_unify_(f1, f2, do_meet) for (f1, f2) in zip(t1.ops_dot_ordered, t2.ops_dot_ordered)]
    res_type = TAppTag(all_ress .|> x->x.res_type)
    errors = findall((x->x isa TermTagwError), res_type.ops_dot_ordered)
    if length(errors) > 0 res_type = TermTagwError(res_type, "E"*join(errors .|> string, "")) end
    MeetJoin_rec_res(res_type, vcat((all_ress .|> x->x.cs)...))
end

function meetjoin_rec_unify_(t1::TProdTag, t2::TProdTag, do_meet::Bool)::MeetJoin_rec_res
    t1l, t2l = t1.data|>length, t2.data|>length
    all_ress = [meetjoin_rec_unify_(f1, f2, do_meet) for (f1, f2) in zip(t1.data, t2.data)] # Potentially turn into a monad (not really urgent tho)
    res_types = all_ress .|> x->x.res_type
    errors = findall((x->x isa TermTagwError), res_types)
    if t1l != t2l && do_meet
        additional_elems = (t1l>t2l) ? (t1.data[(t2l+1):end]) : (t2.data[(t1l+1):end])
        res_types = vcat(res_types, additional_elems)
    end
    res_type = TProdTag(res_type)
    if length(errors) > 0 res_type = TermTagwError(res_type, "E"*join(errors .|> string, "")) end
    MeetJoin_rec_res(res_type, vcat((all_ress .|> x->x.cs)...))
end

function meetjoin_rec_unify_(t1::TSumTag, t2::TSumTag, do_meet)::MeetJoin_rec_res
    t1l, t2l = t1.data|>length, t2.data|>length
    all_ress = [meetjoin_rec_unify_(f1, f2, do_meet) for (f1, f2) in zip(t1.data, t2.data)] # Potentially turn into a monad (not really urgent tho)
    res_types = all_ress .|> x->x.res_type
    errors = findall((x->x isa TermTagwError), res_types)
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
    res_type = TTermTag(res_in.res_type, res_out.res_type)
    in_err, out_err = (res_in.res_type isa TermTagwError), (res_out.res_type isa TermTagwError)
    if in_err || out_err res_type = TermTagwError(res_type, "E"*(in_err ? "in" : "")*(out_err ? "out" : "")) end
    MeetJoin_rec_res(res_type, vcat(res_out.cs, res_in.cs))
end

function meetjoin_rec_unify_(t1::TSumTerm, t2::TSumTerm, do_meet)::MeetJoin_rec_res
    if t1.tag != t2.tag
        return MeetJoin_rec_res(TermTagwError(t1, Error(err_msg_sumtags(t1, t2))), Array{EqConstraint}[])
        # ^ You MIGHT want to return constraints for t1 and t2 all the same, but i'm NOT doing it...
    else
        res = meetjoin_rec_unify_(t1.data, t2.data, do_meet) # Wait.... Is this even right? How does a type-level sum play with type-level Locs ???
        if res.res_type isa TermTagwError
            return MeetJoin_rec_res(TermTagwError(TSumTerm(t1.tag, t1.tag_name, res.res_type), "E"), res.cs)
        else
            return MeetJoin_rec_res(TSumTerm(t1.tag, t1.tag_name, res.res_type), res.cs)
        end
    end
end
function meetjoin_rec_unify_(t1::TermTag, t2::TSumTerm, do_meet)::MeetJoin_rec_res
    # This behaviour is pretty weird admiddetly, and it simply says: SCREW TAG, essentially
    if (t1 isa TLocTag) MeetJoin_rec_res(t1, Array{EqConstraint}([EqConstraint(t1, t2)]))
    else
        res = meetjoin_rec_unify_(t1, t2.data, do_meet) # Wait.... Is this even right? How does a type-level sum play with type-level Locs ???
        if res isa Error return res end
        MeetJoin_rec_res(TSumTerm(t2.tag, t1.tag_name, res.res_type), res.cs)
    end
end
function meetjoin_rec_unify_(t1::TSumTerm, t2::TermTag, do_meet)::MeetJoin_rec_res
    # This behaviour is pretty weird admiddetly, and it simply says: SCREW TAG, essentially
    if (t2 isa TLocTag) MeetJoin_rec_res(t2, Array{EqConstraint}([EqConstraint(t2, t1)]))
    else
        res = meetjoin_rec_unify_(t1.data, t2, do_meet) # Wait.... Is this even right? How does a type-level sum play with type-level Locs ???
        if res isa Error return res end
        MeetJoin_rec_res(TSumTerm(t1.tag, t1.tag_name, res.res_type), res.cs)
    end
end

function meetjoin_rec_unify_(t1::TLocTag, t2::TLocTag, do_meet)::MeetJoin_rec_res
    MeetJoin_rec_res(
        t2, (t1.var == t2.var) ? Array{EqConstraint}([]) : Array{EqConstraint}([EqConstraint(t1, t2)]))
end

function meetjoin_rec_unify_(t1::TermTag, t2::TermTag, do_meet)::MeetJoin_rec_res # base case
    if t1 == t2 MeetJoin_rec_res(t1, Array{EqConstraint}([]))
    elseif t1 isa TLocTag MeetJoin_rec_res(t1, Array{EqConstraint}([EqConstraint(t1, t2)]))
    elseif t2 isa TLocTag MeetJoin_rec_res(t2, Array{EqConstraint}([EqConstraint(t2, t1)]))
    else Error("Different: $(pr(t1)) is really different from $(pr(t2))")
    end
end

function imply_unify_(t1::TAppTag, t2::TAppTag)::SimpRes
    if length(t1.ops_dot_ordered) != length(t2.ops_dot_ordered)
        Error("Different lambdas: $(length(t1.ops_dot_ordered)) != $(length(t2.ops_dot_ordered))")
    else
        Array{Constraint}([DirectConstraint(s1, s2) for (s1, s2) in zip(t1.ops_dot_ordered, t2.ops_dot_ordered)])
    end
end

function imply_unify_(t1::TProdTag, t2::TProdTag)::SimpRes
    if length(t1.data) < length(t2.data)
        Error("Different lengths: $(length(t1.data)) < $(length(t2.data)), so you cannot even drop.")
    else
        Array{Constraint}([DirectConstraint(s1, s2) for (s1, s2) in zip(t1.data, t2.data)])
    end
    # union([imply_unify_(s1, s2) for (s1, s2) in zip(args1, args2)]...)
    # union((zip(args1, args2) .|> ((a1, a2),)->imply_unify_(a1, a2))...)
    # Array{Constraint}([DirectConstraint(s1, s2) for (s1, s2) in zip(args1.data, args2.data)])
end

function imply_unify_(t1::TAbsTag, t2::TAbsTag)::SimpRes
    println("Simplyfing two Foralls:")
    # FOR NOW, these will be REALLY PICKY
    if t1 == t2
        Array{Constraint}([])
    else
        Error("Different lambdas $(pr(t1)) != $(pr(t2)): I know I'm being picky, but impossible to tell if these are the same: $([t1.body, t2.body])")
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

function imply_unify_(t1::TTermTag, t2::TTermTag)::SimpRes
    Array{Constraint}([
        DirectConstraint(t1.t_out, t2.t_out),
        ReverseConstraint(t1.t_in, t2.t_in)])
end

function imply_unify_(t1::TLocTag, t2::TLocTag)::SimpRes
    Array{Constraint}([DirectConstraint(t1, t2)])
end

function imply_unify_(t1::TSumTag, t2::TSumTag)::SimpRes
    if length(t1.data) > length(t2.data)
        Error("Different lengths: $(length(t1.data)) > $(length(t2.data)), so if you are in the last case you are screwed..")
    else
        Array{Constraint}([DirectConstraint(s1, s2) for (s1, s2) in zip(t1.data, t2.data)])
    end
end

function imply_unify_(t1::TSumTerm, t2::TSumTerm)::SimpRes
    if t1.tag != t2.tag
        Error("For now, you can NEVER unify different tags: $(t1.tag_name) != $(t2.tag_name)")
    else
        Array{Constraint}([DirectConstraint(t1.data, t2.data)])
    end
end
function imply_unify_(t1::TermTag, t2::TSumTerm)::SimpRes
    # This behaviour is pretty weird admiddetly, and it simply says: SCREW TAG, essentially
    if (t1 isa TLocTag) Array{Constraint}([DirectConstraint(t1, t2)])
    else Array{Constraint}([DirectConstraint(t1, t2.data)])
    end
end
function imply_unify_(t1::TSumTerm, t2::TermTag)::SimpRes
    # This behaviour is pretty weird admiddetly, and it simply says: SCREW TAG, essentially
    if (t2 isa TLocTag) Array{Constraint}([DirectConstraint(t1, t2)])
    else Array{Constraint}([DirectConstraint(t1.data, t2)])
    end
end
function imply_unify_(t1::TermTag, t2::TermTag)::SimpRes # base case
    if t1 == t2 Array{Constraint}([])
    elseif typeof(t1) === TLocTag || typeof(t2) === TLocTag Array{Constraint}([DirectConstraint(t1, t2)])
    else Error("Different: $(pr(t1)) is really different from $(pr(t2))")
    end
end

swap(c::DirectConstraint) = ReverseConstraint(c.t2, c.t1)
swap(c::ReverseConstraint) = DirectConstraint(c.t2, c.t1)
imply_unify_(c::DirectConstraint)::SimpRes = imply_unify_(c.t1, c.t2)
function imply_unify_(c::ReverseConstraint)::SimpRes
    res = imply_unify_(c.t2, c.t1)
    (res isa Error) ? res : (Array{Constraint}(res .|> swap))
end









# Unify: solve f(x) = g(y) in the sense of finding x AND y,
# EXCEPT it WONT fail if post-applying some DROPPINGs here and there will help.
# It WONT RETURN THEM, either. See above.

# idea: in NO CASE x=f(x) can be solved, (if types_ are REDUCED), because we handle RecursiveTypes Differently!!
usesLocs(t::TGlobTag)::Array{Index} = Array{Index}([])
usesLocs(t::TLocTag)::Array{Index} = Array{Index}([t.var])
usesLocs(t::TTopTag)::Array{Index} = Array{Index}([])
usesLocs(t::TAppTag)::Array{Index} = unique(vcat((t.ops_dot_ordered .|> usesLocs)...))
usesLocs(t::TProdTag)::Array{Index} = unique(vcat((t.data .|> usesLocs)...))
usesLocs(t::TSumTag)::Array{Index} = unique(vcat((t.data .|> usesLocs)...))
usesLocs(t::TSumTerm)::Array{Index} = t.data |> usesLocs
usesLocs(t::TAbsTag)::Array{Index} = Array{Index}([])
usesLocs(t::TTermTag)::Array{Index} = unique(vcat(t.t_in |> usesLocs, t.t_out |> usesLocs))
function check_not_recursive(tloc::TLocTag, tt::TermTag)::Bool
    for v in usesLocs(tt)
    if tloc.var == v return false end
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

function get_subst_prod(tloc::TLocTag, tt::TermTag, current_arity::Int)::TProdTag
    # resulting_arity = current_arity - 1
    # you have ALREADY TESTED that tt does not contain tloc, that's the whole point !!!!
    prod = vcat(
        Array{TermTag}([TLocTag(i) for i in 1:(tloc.var - 1)]),
        Array{TermTag}([TLocTag(0)]), # Placeholder, complete nonsense, it's getting replaced
        Array{TermTag}([TLocTag(i) for i in (tloc.var:current_arity - 1)])
    )
    prod[tloc.var] = ass_reduc(tt, TProdTag(prod))
    TProdTag(prod)
end

function share_ctx_tlocs_names(t1::TAbsTag, t2::TAbsTag, t1arity::Index, t2arity::Index)
    s1 = TProdTag([TLocTag(i) for i in 1:t1arity])
    s2 = TProdTag([TLocTag(i) for i in (t1arity + 1):(t1arity + t2arity)])
    TAppTag([s1, t1]), TAppTag([s2, t2])
end
function share_ctx_tlocs_names_get_substs(t1arity::Index, t2arity::Index)
    s1 = TProdTag([TLocTag(i) for i in 1:t1arity])
    s2 = TProdTag([TLocTag(i) for i in (t1arity + 1):(t1arity + t2arity)])
    s1, s2
end

struct ItsLiterallyAlreadyOk end

function get_first_pair_of_matching_indices(v::Array{Index})
    for i in 1:length(v)
        for j in i+1:length(v)
            if v[i] == v[j] return (i,j) end
        end
    end
    nothing
end
function get_loc_loc_constraint(v)
    for i in 1:length(v)
        if (v[i].t1 isa TLocTag && v[i].t2 isa TLocTag) return i end
    end
    nothing
end

@enum Unify_mode meet_=1 join_=2 imply_=3

function robinsonUnify(t1::TAbsTag, t2::TAbsTag, t1arity::Index, t2arity::Index; unify_tlocs_ctx::Bool = true, mode::Unify_mode=join_)::Union{Tuple{TProdTag,TProdTag, TermTag},Error, ItsLiterallyAlreadyOk}
    # 1. Share TLocs
    if unify_tlocs_ctx
        current_arity = t1arity + t2arity
        t1, t2 = share_ctx_tlocs_names(t1, t2, t1arity, t2arity)
    else
        # This means Sharing of names has ALREADY HAPPENED !!!
        current_arity = max(t1arity, t2arity)
        t1, t2 = t1.body, t2.body
    end

    # 2. unify term and/or produce Eqconstraints
    if mode==imply_
        STACK = Array{Constraint}([DirectConstraint(t1, t2)])
    else
        t1, t2 = reduc(t1), reduc(t2)
        res = meetjoin_rec_unify_(t1, t2, mode==meet_)
        if res isa Error return res end
        res_type, STACK = res.res_type, res.cs
    end

    # 3. Solve all constraints:
    current_total_subst = Array{TProdTag}([]) # SMART_REDUCED VERSION # (Can be a single [TProdTag] or the whole list)
    # ^ Still, to pass into get_reduc_subst IN THIS ORDER

    # Remove all loc-loc constraint first
    while (i=get_loc_loc_constraint(STACK)) !== nothing
        l1, l2 = STACK[i].t1.var, STACK[i].t2.var
        deleteat!(STACK, i)
        if l1 == l2 continue end # cannot hurt can it?
        var, tt = max(l1, l2), TLocTag(min(l1, l2))
        new_subst = get_subst_prod(TLocTag(var), tt, current_arity)
        current_total_subst = Array{TProdTag}(ass_smart_reduc(current_total_subst..., new_subst))
        current_arity = arity(current_total_subst[end]) # The beauty of this is this is Enough... I HOPE LOL
        for i in 1:length(STACK)
            STACK[i] = ass_reduc(STACK[i], new_subst)
            # ^ Really, this is the EASY way:
            # EACH Constraint GETS >ALL< SUBSTS, ONE BY ONE, FROM THE MOMENT IT ENTERS THE STACK ONWARD.
            # A Better way would be: TRACK When each Contraint enters the stack. When you Consider that contraint,
            # apply to it the PREASSOCIATED CURRENT_TOTAL_SUBST of the substs it missed After it was created !!!
            # (wait.. That doesnt sound easy, as that means you can NEVER preassociate anything ?)
        end
    end

    # This while loop is Important for Meeting, while it can be Skipped for directional case
    # POSSIBLE OPTIMIZATION: Keep the TLocs in STACK Sorted, or even in a Dict ofc
    if mode != imply_
        while (ij = get_first_pair_of_matching_indices(STACK.|> (x->x.t1.var))) !== nothing
            tloc, ct1, ct2 = STACK[ij[1]].t1, STACK[ij[1]].t2, STACK[ij[2]].t2
            if !check_not_recursive(tloc, ct1) return Error("$(tloc) == $(ct1) is not a thing (recursive)") end
            if !check_not_recursive(tloc, ct2) return Error("$(tloc) == $(ct2) is not a thing (recursive)") end
            res = meetjoin_rec_unify_(ct1, ct2, mode==meet_)
            # Wait.. Are you COMPLETELY SURE you NEVER want a !MODE here ??? ??? ??? ???
            if res isa Error return res end
            STACK[ij[1]] = EqConstraint(tloc, res.res_type)
            deleteat!(STACK, ij[2])
            append!(STACK, res.cs)
        end
    end

    # Substitute away all the constrains, one by one
    while (length(STACK) > 0)
        c = pop!(STACK)
        ct1, ct2 = c.t1, c.t2
        if !(ct1 isa TLocTag || ct2 isa TLocTag)
            @assert mode == imply_
            cs_inside = imply_unify_(reduc(c))
            if cs_inside isa Error return cs_inside end
            append!(STACK, cs_inside)
            continue
        elseif ct1 isa TLocTag && ct2 isa TLocTag
            # NOTE: it would be NICE if i reworked Imply_ mode so that this DOESNT happen ... println("Does locloc Still happen? Ever ????? (Here, w/ $(ct1) and $(ct2))")
            var, tt = ct1.var, ct2 # it's ARBITRARY since these names have no meaning anyway
            if var == tt.var continue end # cannot hurt can it?
        elseif ct1 isa TLocTag
            if !check_not_recursive(ct1, ct2) return Error("$(ct1) == $(ct2) is not a thing (recursive)") end
            var, tt = ct1.var, ct2
        elseif ct2 isa TLocTag
            if !check_not_recursive(ct2, ct1) return Error("$(ct2) == $(ct1) is not a thing (recursive)") end
            var, tt = ct2.var, ct1
        end
        new_subst = get_subst_prod(TLocTag(var), tt, current_arity)
        current_total_subst = Array{TProdTag}(ass_smart_reduc(current_total_subst..., new_subst))
        current_arity = arity(current_total_subst[end]) # The beauty of this is this is Enough... I HOPE LOL
        for i in 1:length(STACK)
            STACK[i] = ass_reduc(STACK[i], new_subst)
            # ^ Really, this is the EASY way:
            # EACH EqConstraint GETS >ALL< SUBSTS, ONE BY ONE, FROM THE MOMENT IT ENTERS THE STACK ONWARD.
            # A Better way would be: TRACK When each Contraint enters the stack. When you Consider that contraint,
            # apply to it the PREASSOCIATED CURRENT_TOTAL_SUBST of the substs it missed After it was created !!!
            # (wait.. That doesnt sound easy, as that means you can NEVER preassociate anything ?)
        end
    end

    if length(current_total_subst) == 0
        return ItsLiterallyAlreadyOk()
    end

    final_subst = ass_reduc(current_total_subst...)
    subst1 = TProdTag(final_subst.data[1:t1arity])
    subst2 = if unify_tlocs_ctx TProdTag(final_subst.data[(t1arity + 1):(t1arity + t2arity)]) else subst2 = TProdTag(final_subst.data[1:t2arity]) end
    if (mode == imply_) res_type = TGlobTag("O") # Why nothing: USE >>t2<< ( The Original one, NOT the Shared version)
    else res_type = ass_reduc(res_type, final_subst) end
    return subst1, subst2, res_type
end

# The following handles ALL THE CONFUSION ARISING FROM having or not having the Forall() at random.
robinsonUnify(t1::TAbsTag, t2::TermTag, t1arity::Index, t2arity::Index; unify_tlocs_ctx::Bool = true, mode::Unify_mode=join_) = robinsonUnify(t1, TAbsTag(t2), t1arity, t2arity; unify_tlocs_ctx=unify_tlocs_ctx, mode=mode)
robinsonUnify(t1::TermTag, t2::TAbsTag, t1arity::Index, t2arity::Index; unify_tlocs_ctx::Bool = true, mode::Unify_mode=join_) = robinsonUnify(TAbsTag(t1), t2, t1arity, t2arity; unify_tlocs_ctx=unify_tlocs_ctx, mode=mode)
function robinsonUnify(t1::TermTag, t2::TermTag, t1arity::Index, t2arity::Index; unify_tlocs_ctx::Bool = true, mode::Unify_mode=join_)
    if (t1arity == 0) && (t2arity == 0)
        return (t1 == t2) ? (TProdTag([]), TProdTag([])) : Error(" Not unifiable: $(t1) != $(t2)")
    else
        return robinsonUnify(TAbsTag(t1), TAbsTag(t2), t1arity, t2arity; unify_tlocs_ctx=unify_tlocs_ctx, mode=mode)
    end
end


# All cases WITHOUT precomputed tarities:
robinsonUnify(t1::TAbsTag, t2::TAbsTag; unify_tlocs_ctx::Bool = true, mode::Unify_mode=join_) = robinsonUnify(t1, t2, t1.body |> arity, t2.body |> arity; unify_tlocs_ctx=unify_tlocs_ctx, mode=mode)
robinsonUnify(t1::TAbsTag, t2::TermTag; unify_tlocs_ctx::Bool = true, mode::Unify_mode=join_) = robinsonUnify(t1, TAbsTag(t2), t1.body |> arity, t2 |> arity; unify_tlocs_ctx=unify_tlocs_ctx, mode=mode)
robinsonUnify(t1::TermTag, t2::TAbsTag; unify_tlocs_ctx::Bool = true, mode::Unify_mode=join_) = robinsonUnify(TAbsTag(t1), t2, t1 |> arity, t2.body |> arity; unify_tlocs_ctx=unify_tlocs_ctx, mode=mode)
robinsonUnify(t1::TermTag, t2::TermTag; unify_tlocs_ctx::Bool = true, mode::Unify_mode=join_) = robinsonUnify(TAbsTag(t1), TAbsTag(t2), t1 |> arity, t2 |> arity; unify_tlocs_ctx=unify_tlocs_ctx, mode=mode)




# Type inference

# IMPORTANT: I'm using TTermTag's for carrying around contexts, but PLEASE make sure it's always TTermTag OF A TPROD...

TTermEmpty(res_type::TermTag) = TTermTag(TProdTag([]), res_type)

function infer_type_(term::TLocTag)::Union{TTermTag,Error}
    return TTermTag(TProdTag([TLocTag(i) for i in 1:term.var]), TLocTag(term.var))  # TAbsTag(TLocTag(term.var)) was an idea i tried
end
function infer_type_(term::TGlobTag)::Union{TTermTag,Error}
    if term.type isa TAbsTag return TTermEmpty(term.type.body)
    # ^ This is because TTermTag's are Naked (no Forall) for some reason- BOY will this become a mess
    else return TTermEmpty(term.type) end
end
function infer_type_(term::TTopTag)::Union{TTermTag,Error} return TTermEmpty(TTopTag()) end
function infer_type_(term::TAnnoTag, t_computed::TTermTag)::Union{TTermTag,Error}
    substs = robinsonUnify(t_computed.t_out, term.type, mode=imply_)
    if substs isa Error return substs
    elseif substs isa ItsLiterallyAlreadyOk return TTermTag(t_computed.t_in, term.type)
    end
    s1, s2 = substs
    if term.type isa TAbsTag
        term_type = term.type.body # Oh fuck what am i doing
    else
        term_type = term.type
    end
    if t_computed.t_in.data |> length == 0 # HOPEFULLY this is a Type, NOT a body
        return TTermEmpty(ass_reduc(term_type, s2))
    else
        args = ass_reduc(t_computed.t_in, s1)
        tt = ass_reduc(term_type, s2)
        return TTermTag(args, tt)
    end
end

function infer_type_(term::TProdTag, ts_computed::Array{TTermTag})::Union{TTermTag,Error}
    # IDEA: This checking that all args are the same, really belongs to the DIAGONAL FUNCTOR of terms,
    # but this is a hodgepodge, so that's fine.
    # @assert length(term.data) == length(ts_computed) "$(length(term.data)) != $(length(ts_computed)) in $(term.data) != $(ts_computed)"
    # ^ i REALLY WANT to have this, except that HORRIBLE HACK in infer(TAppTag) passes an EMPTY EPROD here...

    # IDEA: if max_eargs_length == 0, you STILL have to UNIFY the TLocs, which is currenty done by
    # JUST RUNNING robinsonUnify on the Empty prods, and using that behaviour.
    unified_RES_types::Array{TermTag} = Array{TermTag}([ts_computed[1].t_out])
    args, full_arity = ts_computed[1].t_in, ts_computed[1] |> arity
    for t in ts_computed[2:end]
        s1, s2 = share_ctx_tlocs_names_get_substs(full_arity, t |> arity)
        args, t = ass_reduc(args, s1), ass_reduc(t, s2)
        unified_RES_types = unified_RES_types .|> (x -> ass_reduc(x, s1))
        full_arity = max(s1|>arity, s2|>arity)
        res = robinsonUnify(
            TAbsTag(args), TAbsTag(t.t_in), full_arity, full_arity;
            unify_tlocs_ctx=false, mode=meet_)
        if res isa Error
            return Error("ELocs typed $(t.arg_types .|> pr) cannot be unified into ELocs typed $(args.arg_types .|> pr), with error '$(res)'")
        elseif res isa ItsLiterallyAlreadyOk
            push!(unified_RES_types, t.t_out)
            full_arity = max(s1|>arity, s2|>arity)
        else
            s1, s2, meeted = res
            args = meeted
            unified_RES_types = unified_RES_types .|> (x -> ass_reduc(x, s1)) # if they BECAME EQUAL to the stuff "args" comes from, this should work.. No?
            push!(unified_RES_types, ass_reduc(t.t_out, s2))
            full_arity = max(s1|>arity, s2|>arity) # god i HOPE this makes sense.....
        end
    end
    return TTermTag(args, TProdTag(unified_RES_types))
end

function infer_type_(term::TAbsTag, t_computed::TTermTag)::Union{TTermTag,Error}
    return TTermTag(TProdTag([]), t_computed)
end
function infer_type_(term::TSumTerm, t_computed::TTermTag)::Union{TTermTag,Error}
    arT, tag = t_computed |> arity, term.tag
    types = vcat([TLocTag(n) for n in (arT + 1):(arT + tag - 1)], [t_computed.t_out])
    return TTermTag(t_computed.t_in, TAbsTag(TSumTag(types)))
end
function infer_type_(term::TBranchesTag, t_computed::TTermTag)::Union{TTermTag,Error}
    arT, tag = t_computed |> arity, term.tag
    types = vcat([TLocTag(n) for n in (arT + 1):(arT + tag - 1)], [t_computed.t_out])
    return TTermTag(t_computed.t_in, TAbsTag(TSumTag(types)))
end

function infer_type_(term::TAppTag, ts_computed::Array{TTermTag})::Union{TTermTag,Error}
    # First, fix TLocTag's by SQUASHING THEM TO BE TTERMS.
    # Idea: - TAbsTag come as TTErms (TTermTag with NO dependencies)  - ELocs come as InfRes WITH the dependency  - NONE of the TTermTag have a Forall around cuz it's how it is in this mess
    ts_computed_2 = Array{TTermTag}([ts_computed[1]])
    for t in ts_computed[2:end]
        fake_tterm = TAbsTag(TTermTag(TLocTag(1), TLocTag(2)))
        tterm_subst = robinsonUnify(t.t_out, fake_tterm, t |> arity, fake_tterm.body |> arity; mode=imply_)
        if tterm_subst isa Error return Error("Calling a non-function: $(t)")
        elseif tterm_subst isa ItsLiterallyAlreadyOk push!(ts_computed_2, t)
        else push!(ts_computed_2, ass_reduc(t, tterm_subst[1])) # t.t_out SHOULD be nothing else but a TTermTag... RIGTH?
        end
    end
    # ^ Each of these still has ITS OWN TLocTag's

    # Second, Unify the context of the TLocs:
    all_w_unified_args = infer_type_(TProdTag([]), ts_computed_2)
    # ^ REUSING the TProdTag inference, HACKING the fact that TermTag is NOT used
    # What comes out is a: TTermTag(TProdTag([...]), TProdTag(([TTermTag(), ...])))
    full_arity = all_w_unified_args |> arity
    # ^Can i compute this in some smarter way?  # Dunno !
    args, tterms = all_w_unified_args.t_in, all_w_unified_args.t_out.data
    # ^ ts_computed_out becomes array and args remains TProdTag.. What a mess

    # Third, actually unify all in/outs:
    prev_out = tterms[1] # TODO fix when app is not a mess anymore
    for i in 2:length(tterms)
        next_in = tterms[i].t_in # YES this always exists now
        substs =  robinsonUnify(
            TAbsTag(prev_out), TAbsTag(next_in), full_arity, full_arity; unify_tlocs_ctx=false, mode=imply_)
        # TODO: i DONT LIKE these Foralls, it's WRONG, but, it's the only way of accessing unify_tlocs_ctx atm
        if substs isa Error
            return Error("Mismatched app: get out type $(prev_out |> pr) but required type $(next_in |> pr), with error '$(substs)'")
        elseif substs isa ItsLiterallyAlreadyOk
            prev_out = tterms[i].t_out
        else
            (s1, s2) = substs
            # ^ Wait.. Are you telling me, if unify_tlocs_ctx=false, s1 and s2 are ALWAYS the same ???  # # Man, this is a crazy world..
            tterms = ass_reduc(TProdTag(tterms), s1).data
            # ^ the LENGTH of tterms DOES NOT CHANGE HERE
            # ^ Also Maybe you can SKIP updating all of them but who cares
            args = ass_reduc(args, s1) # Keep track of the Arg types, too
            full_arity = s1 |> arity
            prev_out = tterms[i].t_out
        end
    end
    return TTermTag(args, tterms[end].t_out)
    # Returns the OUTPUT type instead of the composed TTermTag type cuz this is a mess
end



# Silly categorical-algebra-ish recursive wrapup:
function infer_type_rec(term::TLocTag)::Union{TTermTag,Error} return infer_type_(term) end
function infer_type_rec(term::TGlobTag)::Union{TTermTag,Error} return infer_type_(term) end
function infer_type_rec(term::TTopTag)::Union{TTermTag,Error} return infer_type_(term) end
function infer_type_rec(term::TAnnoTag)::Union{TTermTag,Error}
    tt = infer_type_rec(term.expr)
    return (tt isa Error) ? tt : infer_type_(term, tt)
end
function infer_type_rec(term::TAbsTag)::Union{TTermTag,Error} tt = infer_type_rec(term.body); return (tt isa Error) ? tt : infer_type_(term, tt) end
function infer_type_rec(term::TProdTag)::Union{TTermTag,Error}
    tts::Array{Union{TTermTag,Error} } = infer_type_rec.(term.data)
    for tt in tts if tt isa Error return tt end end
    return infer_type_(term, Array{TTermTag}(tts))
end
function infer_type_rec(term::TSumTerm)::Union{TTermTag,Error} tt = infer_type_rec(term.data); return (tt isa Error) ? tt : infer_type_(term, tt) end
function infer_type_rec(term::TBranchesTag)::Union{TTermTag,Error}
    tts = infer_type_rec.(term.ops_chances)
    for tt in tts if tt isa Error return tt end end
    return infer_type_(term, Array{TTermTag}(tts))
end
function infer_type_rec(term::TAppTag)::Union{TTermTag,Error}
    tts::Array{Union{TTermTag,Error}} = infer_type_rec.(term.ops_dot_ordered)
    for tt in tts if tt isa Error return tt end end
    return infer_type_(term, Array{TTermTag}(tts))
end


# *unification*, thproving_1.jl, mylambda1_dep.jl