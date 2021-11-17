
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


include("mylambda1.jl")


abstract type Constraint end
struct DirectConstraint <: Constraint # (->)
    t1::Term
    t2::Term
end
struct ReverseConstraint <: Constraint# (Meaning <-)
    t1::Term
    t2::Term
end
struct EqConstraint <: Constraint # Should be equal.
    t1::TLoc
    t2::Term
end
Base.:(==)(a::EqConstraint, b::EqConstraint) = (a.t1 == b.t1) && (a.t2 == b.t2)
Base.:(==)(a::DirectConstraint, b::DirectConstraint) = (a.t1 == b.t1) && (a.t2 == b.t2)
Base.:(==)(a::ReverseConstraint, b::ReverseConstraint) = (a.t1 == b.t1) && (a.t2 == b.t2)
reduc(c::DirectConstraint) = DirectConstraint(reduc(c.t1), reduc(c.t2))
reduc(c::ReverseConstraint) = ReverseConstraint(reduc(c.t1), reduc(c.t2))
reduc(c::EqConstraint) = EqConstraint(reduc(c.t1), reduc(c.t2))


Error = String
Imply_res = Union{Array{Constraint},Error}

pr(c::Constraint)::String = pr(c.t1) * "==" * pr(c.t2)


#a join b  ==  a v b  ==  a<avb, b<avb  ==  a CAN BECOME a join b, b CAN BECOME a join b

struct MeetJoin_rec_res
    res_type::Term # OR would be better if each one had its own?  --> NOTE: maybe i can still template it?
    cs::Array{EqConstraint}
end

function meetjoin_rec_unify_(t1::TApp, t2::TApp, do_meet::Bool)::Union{Error, MeetJoin_rec_res}
    if length(t1.ops_dot_ordered) != length(t2.ops_dot_ordered) return Error("Different lambdas: $(length(t1.ops_dot_ordered)) != $(length(t2.ops_dot_ordered))") end
    res_types, res_cs = Array{Term}([]), Array{EqConstraint}([])
    for (f1, f2) in zip(t1.ops_dot_ordered, t2.ops_dot_ordered) # Potentially turn into a monad (not really urgent tho)
        res = meetjoin_rec_unify_(f1, f2, do_meet)
        if res isa Error return res end
        push!(res_types, res.res_type)
        append!(res_cs, res.cs)
    end
    MeetJoin_rec_res(TApp(res_types), res_cs)
end

function meetjoin_rec_unify_(t1::TProd, t2::TProd, do_meet::Bool)::Union{Error, MeetJoin_rec_res}
    t1l, t2l = t1.data|>length, t2.data|>length
    res_types, res_cs = Array{Term}([]), Array{EqConstraint}([])
    for (f1, f2) in zip(t1.data, t2.data) # Potentially turn into a monad (not really urgent tho)
        res = meetjoin_rec_unify_(f1, f2, do_meet)
        if res isa Error return res end
        push!(res_types, res.res_type)
        append!(res_cs, res.cs)
    end
    if t1l != t2l && do_meet
        additional_elems = (t1l>t2l) ? (t1.data[(t2l+1):end]) : (t2.data[(t1l+1):end])
        res_types = vcat(res_types, additional_elems)
    elseif t1l != t2l && !do_meet
        res_types = res_types # SHOULD work because zip clips already !
    else
        res_types = res_types
    end
    MeetJoin_rec_res(TProd(res_types), res_cs)
end

function meetjoin_rec_unify_(t1::TSum, t2::TSum, do_meet)::Union{Error, MeetJoin_rec_res}
    t1l, t2l = t1.data|>length, t2.data|>length
    res_types, res_cs = Array{Term}([]), Array{EqConstraint}([])
    for (f1, f2) in zip(t1.data, t2.data) # Potentially turn into a monad (not really urgent tho)
        res = meetjoin_rec_unify_(f1, f2, do_meet)
        if res isa Error return res end
        push!(res_types, res.res_type)
        append!(res_cs, res.cs)
    end
    if t1l != t2l && !do_meet
        additional_elems = (t1l>t2l) ? (t1.data[(t2l+1):end]) : (t2.data[(t1l+1):end])
        res_types = vcat(res_types, additional_elems)
    elseif t1l != t2l && do_meet
        res_types = res_types # SHOULD work because zip clips already !
    else
        res_types = res_types
    end
    MeetJoin_rec_res(TSum(res_types), res_cs)
end

function meetjoin_rec_unify_(t1::TAbs, t2::TAbs, do_meet)::Union{Error, MeetJoin_rec_res}
    println("Simplyfing two Foralls:")
    # FOR NOW, these will be REALLY PICKY
    if t1 == t2
        MeetJoin_rec_res(t1, Array{EqConstraint}[])
    else
        Error("Different lambdas $(pr(t1)) != $(pr(t2)): I know I'm being picky, but impossible to tell if these are the same: $([t1.body, t2.body])")
    end
end

function meetjoin_rec_unify_(t1::TTerm, t2::TTerm, do_meet)::Union{Error, MeetJoin_rec_res}
    res_out = meetjoin_rec_unify_(t1.t_out, t2.t_out, do_meet)
    if res_out isa Error return res_out end
    res_in = meetjoin_rec_unify_(t1.t_in, t2.t_in, !do_meet)
    if res_in isa Error return res_in end
    MeetJoin_rec_res(TTerm(res_in.res_type, res_out.res_type), vcat(res_out.cs, res_in.cs))

end

function meetjoin_rec_unify_(t1::TSumTerm, t2::TSumTerm, do_meet)::Union{Error, MeetJoin_rec_res}
    if t1.tag != t2.tag Error("For now, you can NEVER unify different tags: $(t1.tag_name) != $(t2.tag_name)")
    else
        res = meetjoin_rec_unify_(t1.data, t2.data, do_meet) # Wait.... Is this even right? How does a type-level sum play with type-level Locs ???
        if res isa Error return res end
        MeetJoin_rec_res(TSumTerm(t1.tag, t1.tag_name, res.res_type), res.cs)
    end
end
function meetjoin_rec_unify_(t1::Term, t2::TSumTerm, do_meet)::Union{Error, MeetJoin_rec_res}
    # This behaviour is pretty weird admiddetly, and it simply says: SCREW TAG, essentially
    if (t1 isa TLoc) MeetJoin_rec_res(t1, Array{EqConstraint}([EqConstraint(t1, t2)]))
    else
        res = meetjoin_rec_unify_(t1, t2.data, do_meet) # Wait.... Is this even right? How does a type-level sum play with type-level Locs ???
        if res isa Error return res end
        MeetJoin_rec_res(TSumTerm(t2.tag, t1.tag_name, res.res_type), res.cs)
    end
end
function meetjoin_rec_unify_(t1::TSumTerm, t2::Term, do_meet)::Union{Error, MeetJoin_rec_res}
    # This behaviour is pretty weird admiddetly, and it simply says: SCREW TAG, essentially
    if (t2 isa TLoc) MeetJoin_rec_res(t2, Array{EqConstraint}([EqConstraint(t2, t1)]))
    else
        res = meetjoin_rec_unify_(t1.data, t2, do_meet) # Wait.... Is this even right? How does a type-level sum play with type-level Locs ???
        if res isa Error return res end
        MeetJoin_rec_res(TSumTerm(t1.tag, t1.tag_name, res.res_type), res.cs)
    end
end

function meetjoin_rec_unify_(t1::TLoc, t2::TLoc, do_meet)::Union{Error, MeetJoin_rec_res}
    MeetJoin_rec_res(
        t2, (t1.var == t2.var) ? Array{EqConstraint}([]) : Array{EqConstraint}([EqConstraint(t1, t2)]))
end

function meetjoin_rec_unify_(t1::Term, t2::Term, do_meet)::Union{Error, MeetJoin_rec_res} # base case
    if t1 == t2 MeetJoin_rec_res(t1, Array{EqConstraint}([]))
    elseif t1 isa TLoc MeetJoin_rec_res(t1, Array{EqConstraint}([EqConstraint(t1, t2)]))
    elseif t2 isa TLoc MeetJoin_rec_res(t2, Array{EqConstraint}([EqConstraint(t2, t1)]))
    else Error("Different: $(pr(t1)) is really different from $(pr(t2))")
    end
end

function imply_unify_(t1::TApp, t2::TApp)::Imply_res
    if length(t1.ops_dot_ordered) != length(t2.ops_dot_ordered)
        Error("Different lambdas: $(length(t1.ops_dot_ordered)) != $(length(t2.ops_dot_ordered))")
    else
        Array{Constraint}([DirectConstraint(s1, s2) for (s1, s2) in zip(t1.ops_dot_ordered, t2.ops_dot_ordered)])
    end
end

function imply_unify_(t1::TProd, t2::TProd)::Imply_res
    if length(t1.data) < length(t2.data)
        Error("Different lengths: $(length(t1.data)) < $(length(t2.data)), so you cannot even drop.")
    else
        Array{Constraint}([DirectConstraint(s1, s2) for (s1, s2) in zip(t1.data, t2.data)])
    end
    # union([imply_unify_(s1, s2) for (s1, s2) in zip(args1, args2)]...)
    # union((zip(args1, args2) .|> ((a1, a2),)->imply_unify_(a1, a2))...)
    # Array{Constraint}([DirectConstraint(s1, s2) for (s1, s2) in zip(args1.data, args2.data)])
end

function imply_unify_(t1::TAbs, t2::TAbs)::Imply_res
    println("Simplyfing two Foralls:")
    # FOR NOW, these will be REALLY PICKY
    if t1 == t2
        Array{Constraint}([])
    else
        Error("Different lambdas $(pr(t1)) != $(pr(t2)): I know I'm being picky, but impossible to tell if these are the same: $([t1.body, t2.body])")
    end
    # Only accepted case: All constraints are about TLoc only and THE SAME
    # cons = DirectConstraint(t1.body, t2.body)
    # cons = simplify(cons)
    # is_same(c::Constraint) = (c.t1 isa TLoc) && (c.t1 == c.t2)
    # if typeof(cons) == Error
    #     Error("Different lambdas: with this error: $(cons)")
    # elseif length(cons) == 0 || (cons .|> is_same |> all)
    #     Array{Constraint}([])
    # else
    #     Error("Different lambdas $(pr(t1)) != $(pr(t2)): I know I'm being picky, but impossible to simplify this part: $(cons)")
    # end
end

function imply_unify_(t1::TTerm, t2::TTerm)::Imply_res
    Array{Constraint}([
        DirectConstraint(t1.t_out, t2.t_out),
        ReverseConstraint(t1.t_in, t2.t_in)])
end

function imply_unify_(t1::TLoc, t2::TLoc)::Imply_res
    Array{Constraint}([DirectConstraint(t1, t2)])
end

function imply_unify_(t1::TSum, t2::TSum)::Imply_res
    if length(t1.data) > length(t2.data)
        Error("Different lengths: $(length(t1.data)) > $(length(t2.data)), so if you are in the last case you are screwed..")
    else
        Array{Constraint}([DirectConstraint(s1, s2) for (s1, s2) in zip(t1.data, t2.data)])
    end
end

function imply_unify_(t1::TSumTerm, t2::TSumTerm)::Imply_res
    if t1.tag != t2.tag
        Error("For now, you can NEVER unify different tags: $(t1.tag_name) != $(t2.tag_name)")
    else
        Array{Constraint}([DirectConstraint(t1.data, t2.data)])
    end
end
function imply_unify_(t1::Term, t2::TSumTerm)::Imply_res
    # This behaviour is pretty weird admiddetly, and it simply says: SCREW TAG, essentially
    if (t1 isa TLoc) Array{Constraint}([DirectConstraint(t1, t2)])
    else Array{Constraint}([DirectConstraint(t1, t2.data)])
    end
end
function imply_unify_(t1::TSumTerm, t2::Term)::Imply_res
    # This behaviour is pretty weird admiddetly, and it simply says: SCREW TAG, essentially
    if (t2 isa TLoc) Array{Constraint}([DirectConstraint(t1, t2)])
    else Array{Constraint}([DirectConstraint(t1.data, t2)])
    end
end
function imply_unify_(t1::Term, t2::Term)::Imply_res # base case
    if t1 == t2 Array{Constraint}([])
    elseif typeof(t1) === TLoc || typeof(t2) === TLoc Array{Constraint}([DirectConstraint(t1, t2)])
    else Error("Different: $(pr(t1)) is really different from $(pr(t2))")
    end
end

swap(c::DirectConstraint) = ReverseConstraint(c.t2, c.t1)
swap(c::ReverseConstraint) = DirectConstraint(c.t2, c.t1)
imply_unify_(c::DirectConstraint)::Imply_res = imply_unify_(c.t1, c.t2)
function imply_unify_(c::ReverseConstraint)::Imply_res
    res = imply_unify_(c.t2, c.t1)
    (res isa Error) ? res : (Array{Constraint}(res .|> swap))
end









# Unify: solve f(x) = g(y) in the sense of finding x AND y,
# EXCEPT it WONT fail if post-applying some DROPPINGs here and there will help.
# It WONT RETURN THEM, either. See above.

# idea: in NO CASE x=f(x) can be solved, (if types_ are REDUCED), because we handle RecursiveTypes Differently!!
usesLocs(t::TGlob)::Array{Index} = Array{Index}([])
usesLocs(t::TLoc)::Array{Index} = Array{Index}([t.var])
usesLocs(t::TTop)::Array{Index} = Array{Index}([])
usesLocs(t::TApp)::Array{Index} = unique(vcat((t.ops_dot_ordered .|> usesLocs)...))
usesLocs(t::TProd)::Array{Index} = unique(vcat((t.data .|> usesLocs)...))
usesLocs(t::TSum)::Array{Index} = unique(vcat((t.data .|> usesLocs)...))
usesLocs(t::TSumTerm)::Array{Index} = t.data |> usesLocs
usesLocs(t::TAbs)::Array{Index} = Array{Index}([])
usesLocs(t::TTerm)::Array{Index} = unique(vcat(t.t_in |> usesLocs, t.t_out |> usesLocs))
function check_not_recursive(tloc::TLoc, tt::Term)::Bool
    for v in usesLocs(tt)
    if tloc.var == v return false end
    end
    return true
end

get_reduc_subst(t::Array{TProd}) = TApp(vcat([t[end]], t[end - 1:-1:1] .|> (x -> TAbs(x))))
get_reduc_subst(t::Array{Term}) = TApp(vcat([t[end]], t[end - 1:-1:1] .|> (x -> TAbs(x))))
# IMPORTANT: ALL EXCEPT (potentially) the >FIRST< should be TPRODS !!!!!

# ASSOCIATIVE OPERATION to compose the above:
ass_smart_reduc(t...) = (length(t) <= 1) ? (collect(t)) : ([get_reduc_subst(collect(t)) |> reduc])
# TODO: change "[reduc()]" in "smart_reduc" !!
ass_reduc(t::TProd ...)::TProd = (length(t) == 1) ? (t[1]) : (get_reduc_subst(collect(t)) |> reduc)
ass_reduc(t1::Term, ts::TProd ...)::Term = (length(ts) == 0) ? (t1) : (get_reduc_subst(vcat([t1], collect(ts))) |> reduc)

ass_reduc(c::EqConstraint, ts::TProd ...) = EqConstraint(ass_reduc(c.t1, ts...), ass_reduc(c.t2, ts...))
ass_reduc(c::DirectConstraint, ts::TProd ...) = DirectConstraint(ass_reduc(c.t1, ts...), ass_reduc(c.t2, ts...))
ass_reduc(c::ReverseConstraint, ts::TProd ...) = ReverseConstraint(ass_reduc(c.t1, ts...), ass_reduc(c.t2, ts...))

function get_subst_prod(tloc::TLoc, tt::Term, current_arity::Int)::TProd
    # resulting_arity = current_arity - 1
    # you have ALREADY TESTED that tt does not contain tloc, that's the whole point !!!!
    prod = vcat(
        Array{Term}([TLoc(i) for i in 1:(tloc.var - 1)]),
        Array{Term}([TLoc(0)]), # Placeholder, complete nonsense, it's getting replaced
        Array{Term}([TLoc(i) for i in (tloc.var:current_arity - 1)])
    )
    prod[tloc.var] = ass_reduc(tt, TProd(prod))
    TProd(prod)
end

function share_ctx_tlocs_names(t1::TAbs, t2::TAbs, t1arity::Index, t2arity::Index)
    s1 = TProd([TLoc(i) for i in 1:t1arity])
    s2 = TProd([TLoc(i) for i in (t1arity + 1):(t1arity + t2arity)])
    TApp([s1, t1]), TApp([s2, t2])
end
function share_ctx_tlocs_names_get_substs(t1arity::Index, t2arity::Index)
    s1 = TProd([TLoc(i) for i in 1:t1arity])
    s2 = TProd([TLoc(i) for i in (t1arity + 1):(t1arity + t2arity)])
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
        if (v[i].t1 isa TLoc && v[i].t2 isa TLoc) return i end
    end
    nothing
end

@enum Unify_mode meet_=1 join_=2 imply_=3

function robinsonUnify(t1::TAbs, t2::TAbs, t1arity::Index, t2arity::Index; unify_tlocs_ctx::Bool = true, mode::Unify_mode=join_)::Union{Tuple{TProd,TProd, Term},Error, ItsLiterallyAlreadyOk}
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
    current_total_subst = Array{TProd}([]) # SMART_REDUCED VERSION # (Can be a single [TProd] or the whole list)
    # ^ Still, to pass into get_reduc_subst IN THIS ORDER

    # Remove all loc-loc constraint first
    while (i=get_loc_loc_constraint(STACK)) !== nothing
        l1, l2 = STACK[i].t1.var, STACK[i].t2.var
        deleteat!(STACK, i)
        if l1 == l2 continue end # cannot hurt can it?
        var, tt = max(l1, l2), TLoc(min(l1, l2))
        new_subst = get_subst_prod(TLoc(var), tt, current_arity)
        current_total_subst = Array{TProd}(ass_smart_reduc(current_total_subst..., new_subst))
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
        if !(ct1 isa TLoc || ct2 isa TLoc)
            @assert mode == imply_
            cs_inside = imply_unify_(reduc(c))
            if cs_inside isa Error return cs_inside end
            append!(STACK, cs_inside)
            continue
        elseif ct1 isa TLoc && ct2 isa TLoc
            # NOTE: it would be NICE if i reworked Imply_ mode so that this DOESNT happen ... println("Does locloc Still happen? Ever ????? (Here, w/ $(ct1) and $(ct2))")
            var, tt = ct1.var, ct2 # it's ARBITRARY since these names have no meaning anyway
            if var == tt.var continue end # cannot hurt can it?
        elseif ct1 isa TLoc
            if !check_not_recursive(ct1, ct2) return Error("$(ct1) == $(ct2) is not a thing (recursive)") end
            var, tt = ct1.var, ct2
        elseif ct2 isa TLoc
            if !check_not_recursive(ct2, ct1) return Error("$(ct2) == $(ct1) is not a thing (recursive)") end
            var, tt = ct2.var, ct1
        end
        new_subst = get_subst_prod(TLoc(var), tt, current_arity)
        current_total_subst = Array{TProd}(ass_smart_reduc(current_total_subst..., new_subst))
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
    subst1 = TProd(final_subst.data[1:t1arity])
    subst2 = if unify_tlocs_ctx TProd(final_subst.data[(t1arity + 1):(t1arity + t2arity)]) else subst2 = TProd(final_subst.data[1:t2arity]) end
    if (mode == imply_) res_type = TGlob("O") # Why nothing: USE >>t2<< ( The Original one, NOT the Shared version)
    else res_type = ass_reduc(res_type, final_subst) end
    return subst1, subst2, res_type
end

# The following handles ALL THE CONFUSION ARISING FROM having or not having the Forall() at random.
robinsonUnify(t1::TAbs, t2::Term, t1arity::Index, t2arity::Index; unify_tlocs_ctx::Bool = true, mode::Unify_mode=join_) = robinsonUnify(t1, TAbs(t2), t1arity, t2arity; unify_tlocs_ctx=unify_tlocs_ctx, mode=mode)
robinsonUnify(t1::Term, t2::TAbs, t1arity::Index, t2arity::Index; unify_tlocs_ctx::Bool = true, mode::Unify_mode=join_) = robinsonUnify(TAbs(t1), t2, t1arity, t2arity; unify_tlocs_ctx=unify_tlocs_ctx, mode=mode)
function robinsonUnify(t1::Term, t2::Term, t1arity::Index, t2arity::Index; unify_tlocs_ctx::Bool = true, mode::Unify_mode=join_)
    if (t1arity == 0) && (t2arity == 0)
        return (t1 == t2) ? (TProd([]), TProd([])) : Error(" Not unifiable: $(t1) != $(t2)")
    else
        return robinsonUnify(TAbs(t1), TAbs(t2), t1arity, t2arity; unify_tlocs_ctx=unify_tlocs_ctx, mode=mode)
    end
end


# All cases WITHOUT precomputed tarities:
robinsonUnify(t1::TAbs, t2::TAbs; unify_tlocs_ctx::Bool = true, mode::Unify_mode=join_) = robinsonUnify(t1, t2, t1.body |> arity, t2.body |> arity; unify_tlocs_ctx=unify_tlocs_ctx, mode=mode)
robinsonUnify(t1::TAbs, t2::Term; unify_tlocs_ctx::Bool = true, mode::Unify_mode=join_) = robinsonUnify(t1, TAbs(t2), t1.body |> arity, t2 |> arity; unify_tlocs_ctx=unify_tlocs_ctx, mode=mode)
robinsonUnify(t1::Term, t2::TAbs; unify_tlocs_ctx::Bool = true, mode::Unify_mode=join_) = robinsonUnify(TAbs(t1), t2, t1 |> arity, t2.body |> arity; unify_tlocs_ctx=unify_tlocs_ctx, mode=mode)
robinsonUnify(t1::Term, t2::Term; unify_tlocs_ctx::Bool = true, mode::Unify_mode=join_) = robinsonUnify(TAbs(t1), TAbs(t2), t1 |> arity, t2 |> arity; unify_tlocs_ctx=unify_tlocs_ctx, mode=mode)




# Type inference

# IMPORTANT: I'm using TTerm's for carrying around contexts, but PLEASE make sure it's always TTerm OF A TPROD...

TTermEmpty(res_type::Term) = TTerm(TProd([]), res_type)

function infer_type_(term::TLoc)::Union{TTerm,Error}
    return TTerm(TProd([TLoc(i) for i in 1:term.var]), TLoc(term.var))  # TAbs(TLoc(term.var)) was an idea i tried
end
function infer_type_(term::TGlob)::Union{TTerm,Error}
    if term.type isa TAbs return TTermEmpty(term.type.body)
    # ^ This is because TTerm's are Naked (no Forall) for some reason- BOY will this become a mess
    else return TTermEmpty(term.type) end
end
function infer_type_(term::TTop)::Union{TTerm,Error} return TTermEmpty(TTop()) end
function infer_type_(term::TAnno, t_computed::TTerm)::Union{TTerm,Error}
    substs = robinsonUnify(t_computed.t_out, term.type, mode=imply_)
    if substs isa Error return substs
    elseif substs isa ItsLiterallyAlreadyOk return TTerm(t_computed.t_in, term.type)
    end
    s1, s2 = substs
    if term.type isa TAbs
        term_type = term.type.body # Oh fuck what am i doing
    else
        term_type = term.type
    end
    if t_computed.t_in.data |> length == 0 # HOPEFULLY this is a Type, NOT a body
        return TTermEmpty(ass_reduc(term_type, s2))
    else
        args = ass_reduc(t_computed.t_in, s1)
        tt = ass_reduc(term_type, s2)
        return TTerm(args, tt)
    end
end

function infer_type_(term::TProd, ts_computed::Array{TTerm})::Union{TTerm,Error}
    # IDEA: This checking that all args are the same, really belongs to the DIAGONAL FUNCTOR of terms,
    # but this is a hodgepodge, so that's fine.
    # @assert length(term.data) == length(ts_computed) "$(length(term.data)) != $(length(ts_computed)) in $(term.data) != $(ts_computed)"
    # ^ i REALLY WANT to have this, except that HORRIBLE HACK in infer(TApp) passes an EMPTY EPROD here...

    # IDEA: if max_eargs_length == 0, you STILL have to UNIFY the TLocs, which is currenty done by
    # JUST RUNNING robinsonUnify on the Empty prods, and using that behaviour.
    unified_RES_types::Array{Term} = Array{Term}([ts_computed[1].t_out])
    args, full_arity = ts_computed[1].t_in, ts_computed[1] |> arity
    for t in ts_computed[2:end]
        s1, s2 = share_ctx_tlocs_names_get_substs(full_arity, t |> arity)
        args, t = ass_reduc(args, s1), ass_reduc(t, s2)
        unified_RES_types = unified_RES_types .|> (x -> ass_reduc(x, s1))
        full_arity = max(s1|>arity, s2|>arity)
        res = robinsonUnify(
            TAbs(args), TAbs(t.t_in), full_arity, full_arity;
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
    return TTerm(args, TProd(unified_RES_types))
end

function infer_type_(term::TAbs, t_computed::TTerm)::Union{TTerm,Error}
    return TTerm(TProd([]), t_computed)
end
function infer_type_(term::TSumTerm, t_computed::TTerm)::Union{TTerm,Error}
    arT, tag = t_computed |> arity, term.tag
    types = vcat([TLoc(n) for n in (arT + 1):(arT + tag - 1)], [t_computed.t_out])
    return TTerm(t_computed.t_in, TAbs(TSum(types)))
end
function infer_type_(term::TBranches, t_computed::TTerm)::Union{TTerm,Error}
    arT, tag = t_computed |> arity, term.tag
    types = vcat([TLoc(n) for n in (arT + 1):(arT + tag - 1)], [t_computed.t_out])
    return TTerm(t_computed.t_in, TAbs(TSum(types)))
end

function infer_type_(term::TApp, ts_computed::Array{TTerm})::Union{TTerm,Error}
    # First, fix TLoc's by SQUASHING THEM TO BE TTERMS.
    # Idea: - TAbs come as TTErms (TTerm with NO dependencies)  - ELocs come as InfRes WITH the dependency  - NONE of the TTerm have a Forall around cuz it's how it is in this mess
    ts_computed_2 = Array{TTerm}([ts_computed[1]])
    for t in ts_computed[2:end]
        fake_tterm = TAbs(TTerm(TLoc(1), TLoc(2)))
        tterm_subst = robinsonUnify(t.t_out, fake_tterm, t |> arity, fake_tterm.body |> arity; mode=imply_)
        if tterm_subst isa Error return Error("Calling a non-function: $(t)")
        elseif tterm_subst isa ItsLiterallyAlreadyOk push!(ts_computed_2, t)
        else push!(ts_computed_2, ass_reduc(t, tterm_subst[1])) # t.t_out SHOULD be nothing else but a TTerm... RIGTH?
        end
    end
    # ^ Each of these still has ITS OWN TLoc's

    # Second, Unify the context of the TLocs:
    all_w_unified_args = infer_type_(TProd([]), ts_computed_2)
    # ^ REUSING the TProd inference, HACKING the fact that Term is NOT used
    # What comes out is a: TTerm(TProd([...]), TProd(([TTerm(), ...])))
    full_arity = all_w_unified_args |> arity
    # ^Can i compute this in some smarter way?  # Dunno !
    args, tterms = all_w_unified_args.t_in, all_w_unified_args.t_out.data
    # ^ ts_computed_out becomes array and args remains TProd.. What a mess

    # Third, actually unify all in/outs:
    prev_out = tterms[1] # TODO fix when app is not a mess anymore
    for i in 2:length(tterms)
        next_in = tterms[i].t_in # YES this always exists now
        substs =  robinsonUnify(
            TAbs(prev_out), TAbs(next_in), full_arity, full_arity; unify_tlocs_ctx=false, mode=imply_)
        # TODO: i DONT LIKE these Foralls, it's WRONG, but, it's the only way of accessing unify_tlocs_ctx atm
        if substs isa Error
            return Error("Mismatched app: get out type $(prev_out |> pr) but required type $(next_in |> pr), with error '$(substs)'")
        elseif substs isa ItsLiterallyAlreadyOk
            prev_out = tterms[i].t_out
        else
            (s1, s2) = substs
            # ^ Wait.. Are you telling me, if unify_tlocs_ctx=false, s1 and s2 are ALWAYS the same ???  # # Man, this is a crazy world..
            tterms = ass_reduc(TProd(tterms), s1).data
            # ^ the LENGTH of tterms DOES NOT CHANGE HERE
            # ^ Also Maybe you can SKIP updating all of them but who cares
            args = ass_reduc(args, s1) # Keep track of the Arg types, too
            full_arity = s1 |> arity
            prev_out = tterms[i].t_out
        end
    end
    return TTerm(args, tterms[end].t_out)
    # Returns the OUTPUT type instead of the composed TTerm type cuz this is a mess
end



# Silly categorical-algebra-ish recursive wrapup:
function infer_type_rec(term::TLoc)::Union{TTerm,Error} return infer_type_(term) end
function infer_type_rec(term::TGlob)::Union{TTerm,Error} return infer_type_(term) end
function infer_type_rec(term::TTop)::Union{TTerm,Error} return infer_type_(term) end
function infer_type_rec(term::TAnno)::Union{TTerm,Error}
    tt = infer_type_rec(term.expr)
    return (tt isa Error) ? tt : infer_type_(term, tt)
end
function infer_type_rec(term::TAbs)::Union{TTerm,Error} tt = infer_type_rec(term.body); return (tt isa Error) ? tt : infer_type_(term, tt) end
function infer_type_rec(term::TProd)::Union{TTerm,Error}
    tts::Array{Union{TTerm,Error} } = infer_type_rec.(term.data)
    for tt in tts if tt isa Error return tt end end
    return infer_type_(term, Array{TTerm}(tts))
end
function infer_type_rec(term::TSumTerm)::Union{TTerm,Error} tt = infer_type_rec(term.data); return (tt isa Error) ? tt : infer_type_(term, tt) end
function infer_type_rec(term::TBranches)::Union{TTerm,Error}
    tts = infer_type_rec.(term.ops_chances)
    for tt in tts if tt isa Error return tt end end
    return infer_type_(term, Array{TTerm}(tts))
end
function infer_type_rec(term::TApp)::Union{TTerm,Error}
    tts::Array{Union{TTerm,Error}} = infer_type_rec.(term.ops_dot_ordered)
    for tt in tts if tt isa Error return tt end end
    return infer_type_(term, Array{TTerm}(tts))
end


# *unification*, thproving_1.jl, mylambda1_dep.jl