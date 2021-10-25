
# higher order typechecker using unification: Like unification.jl, but using my mylambda machinery

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

usesLocs(t::TGlob)::Array{Index} = Array{Index}([])
usesLocs(t::TLoc)::Array{Index} = Array{Index}([t.var])
usesLocs(t::TTop)::Array{Index} = Array{Index}([])
usesLocs(t::TApp)::Array{Index} = unique(vcat((t.ops_dot_ordered .|> usesLocs)...))
usesLocs(t::TProd)::Array{Index} = unique(vcat((t.data .|> usesLocs)...))
usesLocs(t::TSum)::Array{Index} = unique(vcat((t.data .|> usesLocs)...))
usesLocs(t::TSumTerm)::Array{Index} = t.data |> usesLocs
usesLocs(t::TForall)::Array{Index} = Array{Index}([])
usesLocs(t::TTerm)::Array{Index} = unique(vcat(t.t_in |> usesLocs, t.t_out |> usesLocs))


########################################## SIMPLIFY

# ((question is: RECURSIVE(call simplify_) OR MANAGED (return constrains)?
# you HAVE TO CHOSE BECAUSE YOU DON'T HAVE A MONAD.......            (i think) ))


# (Each of these means: Simplify the constraint "t1 must be == t2").

# Here, I'm Shamelessly faking having DIRECTIONAL unification
# (Ie, if i have types A and B, CAN A become B via a function that turns A into B?)
# using this rationale: if Both A and B can become T via suitable funcs a and b,
# then T (the UNIFIED one) is the good one, and YES A can become T via a.
# Furthermore: if A and B are TTerms, remember that in order to work, the B ARG(S) have to become the A arg(s).
# Furthermore: Suppose A is the INFERENCED one, B is the ANNOTATED one.
# THIS is the order you want, the INFERENCED one must become the ANNOTATED one.
# NOTE, that THIS IS GOOD because if the annotated one has lots of args and the inferenced one has few, you can DROP them.
# ALSO NOTE, that if you have a shared T, it will have LOTS of params as the Annotated one,
# and YES, A Can become T via (reverse) dropping.

# Also, the idea is this: If you are trying to make A->C become B->D,
# there are TWO things you can do to find a SHARED T->V :
# You can PREAPPLY substs, X->Y->A->C or W->Z->B->D,
# or you can POST apply stuff, eg DROPPING operations, A->C->1->2 or B->D->3->4.
# I'm collecting ALL the PREAPPLICATIONS as substs/constraints/ass_reduc terms,
# but i'm IMPLICITELY DROPPING ALL THE POST APPLIED STUFF.

# Also: when i need to, in the post way, I'm only applying SIMPLE DROP/PROJECTION OPERATIONS,
# and ONLY TO the FIRST one, A->C. Otherwise, too easy, you can always drop everything to [].
# BUT, for the twisted/asymmetric ass way Constructors/contexts are encoded here,
# those projections operations can immediatly get NESTED, and be very hard to recover ...

# What i am doing is: i have this Directional simplification,
# where you can collect Substs Actions on the LEFT (first) side of A->B,
# but NOT Dropping Actions on the RIGHT(second) side,

# which means you CANNOT recover T by APPLYING the b to B ? Maybe ?
# Prob not, because what about when you covariantly switch?

# ->> The reason y i have these ReverseContraint and Swap()'s like this, is:
# that EVERYTHING IN THE 1ST POSITION ALWAYS REFER TO THE 1ST CONTEXT,
# AND EVERYTHING IN THE 2ND POSITION ALWAYS REFER TO THE 2ND CONTEXT.
# It's a matter of stupid contexts, like this.

# >> I mean how does
# t1 = TProd([TTerm(TProd([TLoc(1)]), TGlob("Z")), TGlob("T")])
# becomes
# t2 = TProd([TTerm(TProd([TGlob("A"), TLoc(2)]), TGlob("Z")), TGlob("T")])
# :
# Sure, Constraint(TLoc(1), TGlob("A")) which can become the nice ass_reduc application
# tt1 = ass_reduc(t1, TProd([TGlob("A")]))
# But then, you have to POST apply a DROPPING operation on T2, which WONT HAPPEN rn .....


abstract type Constraint end
struct DirectConstraint <: Constraint # (->)
    t1::Type_
    t2::Type_
end
struct ReverseConstraint <: Constraint# (Meaning <-)
    t1::Type_
    t2::Type_
end
Base.:(==)(a::DirectConstraint, b::DirectConstraint) = (a.t1 == b.t1) && (a.t2 == b.t2)
Base.:(==)(a::ReverseConstraint, b::ReverseConstraint) = (a.t1 == b.t1) && (a.t2 == b.t2)
reduc(c::DirectConstraint) = DirectConstraint(reduc(c.t1), reduc(c.t2))
reduc(c::ReverseConstraint) = ReverseConstraint(reduc(c.t1), reduc(c.t2))


Error = String
SimpRes = Union{Array{Constraint},Error}

pr(c::Constraint)::String = pr(c.t1) * "==" * pr(c.t2)
just_pr(c::Constraint)::String = just_pr(c.t1) * "==" * just_pr(c.t2)

function simplify_(t1::TApp, t2::TApp)::SimpRes
    @assert t1.ops_dot_ordered |> length == 2 && t2.ops_dot_ordered |> length == 2  # TEMPORARY
    @assert t1.ops_dot_ordered[1] isa TProd && t2.ops_dot_ordered[1] isa TProd
    if length(t1.ops_dot_ordered) != length(t2.ops_dot_ordered)
        Error("Different lambdas: $(length(t1.ops_dot_ordered)) != $(length(t2.ops_dot_ordered))")
    else
        Array{Constraint}([DirectConstraint(s1, s2) for (s1, s2) in zip(t1.ops_dot_ordered, t2.ops_dot_ordered)])
    end
end

function simplify_(t1::TProd, t2::TProd)::SimpRes
    if length(t1.data) < length(t2.data)
        Error("Different lengths: $(length(t1.data)) < $(length(t2.data)), so you cannot even drop.")
    else
        Array{Constraint}([DirectConstraint(s1, s2) for (s1, s2) in zip(t1.data, t2.data)])
    end
    # union([simplify_(s1, s2) for (s1, s2) in zip(args1, args2)]...)
    # union((zip(args1, args2) .|> ((a1, a2),)->simplify_(a1, a2))...)
    # Array{Constraint}([DirectConstraint(s1, s2) for (s1, s2) in zip(args1.data, args2.data)])
end

function simplify_(t1::TForall, t2::TForall)::SimpRes
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

function simplify_(t1::TTerm, t2::TTerm)::SimpRes
    Array{Constraint}([
        DirectConstraint(t1.t_out, t2.t_out),
        ReverseConstraint(t1.t_in, t2.t_in)])
end

function simplify_(t1::TLoc, t2::TLoc)::SimpRes
    Array{Constraint}([DirectConstraint(t1, t2)])
end

function simplify_(t1::TSum, t2::TSum)::SimpRes
    if length(t1.data) > length(t2.data)
        Error("Different lengths: $(length(t1.data)) > $(length(t2.data)), so if you are in the last case you are screwed..")
    else
        Array{Constraint}([DirectConstraint(s1, s2) for (s1, s2) in zip(t1.data, t2.data)])
    end
end

function simplify_(t1::TSumTerm, t2::TSumTerm)::SimpRes
    if t1.tag != t2.tag
        Error("For now, you can NEVER unify different tags: $(t1.tag) != $(t2.tag)")
    else
        Array{Constraint}([DirectConstraint(t1.data, t2.data)])
    end
end
function simplify_(t1::Type_, t2::TSumTerm)::SimpRes
    # This behaviour is pretty weird admiddetly, and it simply says: SCREW TAG, essentially
    if (t1 isa TLoc) Array{Constraint}([DirectConstraint(t1, t2)])
    else Array{Constraint}([DirectConstraint(t1, t2.data)])
    end
end
function simplify_(t1::TSumTerm, t2::Type_)::SimpRes
    # This behaviour is pretty weird admiddetly, and it simply says: SCREW TAG, essentially
    if (t2 isa TLoc) Array{Constraint}([DirectConstraint(t1, t2)])
    else Array{Constraint}([DirectConstraint(t1.data, t2)])
    end
end
function simplify_(t1::Type_, t2::Type_)::SimpRes # base case
    if t1 == t2 Array{Constraint}([])
    elseif typeof(t1) === TLoc || typeof(t2) === TLoc Array{Constraint}([DirectConstraint(t1, t2)])
    else Error("Different: $(just_pr(t1)) is really different from $(just_pr(t2))")
    end
end

swap(c::DirectConstraint) = ReverseConstraint(c.t2, c.t1)
swap(c::ReverseConstraint) = DirectConstraint(c.t2, c.t1)
simplify_(c::DirectConstraint)::SimpRes = simplify_(c.t1, c.t2)
function simplify_(c::ReverseConstraint)::SimpRes
    res = simplify_(c.t2, c.t1)
    (res isa Error) ? res : (Array{Constraint}(res .|> swap))
end

# I ELIMINATED BACKTRACK
# function backtrack(array::SimpRes)::SimpRes
#     if typeof(array) === Error
#         return array
#     end
#     reduced = Set{Constraint}([])
#     while length(array) > 0
#         array2 = Array{Constraint}([])
#         for c in array
#             cs = simplify_(c)
#             if typeof(cs) === Error return cs
#             elseif length(cs) == 1 && cs[1] == c push!(reduced, c)
#             elseif length(cs) != 0 append!(array2, cs) end
#         end
#         array = array2
#     end
#     return Array{Constraint}([reduced...])
# end
# function simplify(t1::Type_, t2::Type_)::SimpRes  # simply the toplevel interface
#     t1 = reduc(t1)
#     t2 = reduc(t2)
#     return backtrack(Array{Constraint}([DirectConstraint(t1, t2)]))
#     # array=[Constraint(t1, t2)]
# end
# simplify(c::Constraint)::SimpRes = simplify(c.t1, c.t2)
# simplify(c::Constraint)::SimpRes = simplify(c.t1, c.t2)
# I ELIMINATED BACKTRACK



# Unify: solve f(x) = g(y) in the sense of finding x AND y,
# EXCEPT it WONT fail if post-applying some DROPPINGs here and there will help.
# It WONT RETURN THEM, either. See above.

Subst = Dict{Index,Type_}  # I'm using this as a SPARSE VECTOR

# idea: in NO CASE x=f(x) can be solved, (if types_ are REDUCED), because we handle RecursiveTypes Differently!!
function check_not_recursive(tloc::TLoc, tt::Type_)::Bool
    for v in usesLocs(tt)
    if tloc.var == v return false end
    end
    return true
end


get_reduc_subst(t::Array{TProd}) = TApp(vcat([t[end]], t[end - 1:-1:1] .|> (x -> TForall(x))))
get_reduc_subst(t::Array{Type_}) = TApp(vcat([t[end]], t[end - 1:-1:1] .|> (x -> TForall(x))))
# IMPORTANT: ALL EXCEPT (potentially) the >FIRST< should be TPRODS !!!!!

# ASSOCIATIVE OPERATION to compose the above:
ass_smart_reduc(t...) = (length(t) <= 1) ? (collect(t)) : ([get_reduc_subst(collect(t)) |> reduc])
# TODO: change "[reduc()]" in "smart_reduc" !!
ass_reduc(t::TProd ...)::TProd = (length(t) == 1) ? (t[1]) : (get_reduc_subst(collect(t)) |> reduc)
ass_reduc(t1::Type_, ts::TProd ...)::Type_ = (length(ts) == 0) ? (t1) : (get_reduc_subst(vcat([t1], collect(ts))) |> reduc)


ass_reduc(c::DirectConstraint, ts::TProd ...) = DirectConstraint(ass_reduc(c.t1, ts...), ass_reduc(c.t2, ts...))
ass_reduc(c::ReverseConstraint, ts::TProd ...) = ReverseConstraint(ass_reduc(c.t1, ts...), ass_reduc(c.t2, ts...))

function get_subst_prod(tloc::TLoc, tt::Type_, current_arity::Int)::TProd
    # resulting_arity = current_arity - 1
    # you have ALREADY TESTED that tt does not contain tloc, that's the whole point !!!!
    prod = vcat(
        Array{Type_}([TLoc(i) for i in 1:(tloc.var - 1)]),
        Array{Type_}([TLoc(0)]), # Placeholder, complete nonsense, it's getting replaced
        Array{Type_}([TLoc(i) for i in (tloc.var:current_arity - 1)])
    )
    prod[tloc.var] = ass_reduc(tt, TProd(prod))
    TProd(prod)
end


function robinsonUnify(t1::TForall, t2::TForall, t1arity::Index, t2arity::Index; unify_tlocs_ctx::Bool = true)::Union{Tuple{TProd,TProd},Error}
    # I maybe i can improve this a bit, not now tho:

    if unify_tlocs_ctx
        # IDEA: The following s1 and s2 are ALSO used in a case where t1 and t2 contain EMPTY PROD, in which case they are returned (see below) but EVERYTHING works.
        # >>STILL, you might want to create a different function..
        current_arity = t1arity + t2arity
        s1 = TProd([TLoc(i) for i in 1:t1arity])
        t1 = TApp([s1, t1])
        s2 = TProd([TLoc(i) for i in (t1arity + 1):(t1arity + t2arity)])
        t2 = TApp([s2, t2])
    else
        # This means Unification has ALREADY HAPPENED !!!
        t1, t2 = t1.body, t2.body
        s1, s2 = TProd([TLoc(i) for i in 1:t1arity]), TProd([TLoc(i) for i in 1:t2arity])
        current_arity = max(t1arity, t2arity)
    end

    # Note that now everything is Shared # Also note this is always Dirsect constraint
    t1 = reduc(t1)
    t2 = reduc(t2)
    # Note that the below WERE Reduced before:
    cs = simplify_(t1, t2) # Note they are Already bodies, at this point
    if cs isa Error return cs end
    STACK = cs

    current_total_subst =  Array{TProd}([]) # SMART_REDUCED VERSION # (Can be a single [TProd] or the whole list)
    # ^ Still, to pass into get_reduc_subst IN THIS ORDER

    while (length(STACK) > 0)
        c = pop!(STACK)
        if c isa Error
            return c
        end
        ct1, ct2 = c.t1, c.t2

        if ct1 isa TLoc && ct2 isa TLoc
            i, tt = ct1.var, ct2 # it's ARBITRARY since these names have no meaning anyway
        elseif ct1 isa TLoc
            if !check_not_recursive(ct1, ct2) return Error("$(ct1) == $(ct2) is not a thing (recursive)") end
            # middle_subst[ct1.var] = ct2
            i, tt = ct1.var, ct2
        elseif ct2 isa TLoc
            if !check_not_recursive(ct2, ct1) return Error("$(ct2) == $(ct1) is not a thing (recursive)") end
            # middle_subst[ct2.var] = ct1
            i, tt = ct2.var, ct1
        else
            c = reduc(c)
            cs_inside = simplify_(c)
            if cs_inside isa Error return cs_inside end
            append!(STACK, cs_inside)
            continue
        end
        new_subst = get_subst_prod(TLoc(i), tt, current_arity)
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

    if length(current_total_subst) == 0
        # @assert (t1arity == t2arity) "$(t1arity) != $(t2arity), HOW tho ..."
        # ^ This assert makes sense EVERY TIME THERE'S NO PASSED ARITIES
        # TODO: remove this dumb shit, replace with LITERALLY NOTHING
        return s1, s2
    end

    final_subst = ass_reduc(current_total_subst...)
    subst1 = TProd(final_subst.data[1:t1arity])
    if unify_tlocs_ctx
        subst2 = TProd(final_subst.data[(t1arity + 1):(t1arity + t2arity)])
    else
        subst2 = TProd(final_subst.data[1:t2arity])
    end
    return subst1, subst2
end

# The following handles ALL THE CONFUSION ARISING FROM having or not having the Forall() at random.
robinsonUnify(t1::TForall, t2::Type_, t1arity::Index, t2arity::Index) = robinsonUnify(t1, TForall(t2), t1arity, t2arity)
robinsonUnify(t1::Type_, t2::TForall, t1arity::Index, t2arity::Index) = robinsonUnify(TForall(t1), t2, t1arity, t2arity)
function robinsonUnify(t1::Type_, t2::Type_, t1arity::Index, t2arity::Index)
    if (t1arity == 0) && (t2arity == 0)
        return (t1 == t2) ? (TProd([]), TProd([])) : Error(" Not unifiable: $(t1) != $(t2)")
    else
        return robinsonUnify(TForall(t1), TForall(t2), t1arity, t2arity)
    end
end


# All cases WITHOUT precomputed tarities:
robinsonUnify(t1::TForall, t2::TForall) = robinsonUnify(t1, t2, t1.body |> arity, t2.body |> arity)
robinsonUnify(t1::TForall, t2::Type_) = robinsonUnify(t1, TForall(t2), t1.body |> arity, t2 |> arity)
robinsonUnify(t1::Type_, t2::TForall) = robinsonUnify(TForall(t1), t2, t1 |> arity, t2.body |> arity)
robinsonUnify(t1::Type_, t2::Type_) = robinsonUnify(TForall(t1), TForall(t2), t1 |> arity, t2 |> arity)


struct Inf_res
    # IDEA: you can ALWAYS turn this into a TTerm !
    # Other idea: this is always BARE, ie with NO Forall around. This is because it should be around BOTHthe args and the res!
    arg_types::Array{Type_} # IDEA: you can always turn this into a TProd
    res_type::Type_
end
pr(i::Inf_res) = "Given [$(join(i.arg_types .|>pr, ", "))], get $(i.res_type|>pr)"
Inf_res(res_type::Type_) = Inf_res([], res_type)
Base.:(==)(a::Inf_res, b::Inf_res) = Base.:(==)(a.arg_types, b.arg_types) && Base.:(==)(a.res_type, b.res_type)
ass_reduc(ir::Inf_res, t::TProd ...) = Inf_res(ass_reduc(TProd(ir.arg_types), t...).data, ass_reduc(ir.res_type, t...))
arity(ir::Inf_res) = max(
    (length(ir.arg_types) > 0) ? (ir.arg_types .|> arity |> maximum) : 0, # Yee! Dynamic typing!!
    ir.res_type |> arity)
pad_elocs(elocs::Array{Type_}, max_t_arity::Int, max_length::Int)::Array{Type_} = vcat(elocs, [TLoc(i + max_t_arity) for i in 1:(max_length - length(elocs))])

function infer_type_(term::ELoc)::Union{Inf_res,Error}
    return Inf_res(
        Array{Type_}([TLoc(i) for i in 1:term.n]),
        # TForall(TLoc(term.n))
TLoc(term.n)
    )
end
function infer_type_(term::EGlob)::Union{Inf_res,Error}
    if term.type isa TForall return Inf_res(term.type.body)
    # ^ This is because Inf_res's are Naked (no Forall) for some reason- BOY will this become a mess
    else return Inf_res(term.type) end
end
function infer_type_(term::EUnit)::Union{Inf_res,Error} return Inf_res(TTop()) end
function infer_type_(term::EAnno, t_computed::Inf_res)::Union{Inf_res,Error}
    substs = robinsonUnify(t_computed.res_type, term.type)
    if substs isa Error return substs end
    s1, s2 = substs
    if term.type isa TForall
        term_type = term.type.body # Oh fuck what am i doing
    else
        term_type = term.type
    end
    if t_computed.arg_types |> length == 0 # HOPEFULLY this is a Type, NOT a body
        return Inf_res(ass_reduc(term_type, s2))
    else
        println("Term: ", term)
        println("Term pr: ", term|>pr)
        println("Term type with subst: ", ass_reduc(term_type, s2))
        println("Term type with subst pr: ", ass_reduc(term_type, s2) |> pr)

        println("t_computed res: ", t_computed.res_type)
        println("t_computed res pr: ", t_computed.res_type|>pr)
        println("t_computed res pr red: ", t_computed.res_type|>reduc|>pr)

        println("t_computed res with subst: ", ass_reduc(t_computed.res_type, s1))
        println("t_computed res with subst pr: ", ass_reduc(t_computed.res_type, s1)|>pr)

        println("t_computed args: ", t_computed.arg_types)
        println("t_computed args pr: ", t_computed.arg_types .|> pr)

        println("t_computed args with subst: ", ass_reduc(TProd(t_computed.arg_types), s1))
        println("t_computed args with subst pr: ", ass_reduc(TProd(t_computed.arg_types), s1)|>pr)

        println("\n", "Imean does this ever even happen?")
        args = ass_reduc(TProd(t_computed.arg_types), s1).data
        tt = ass_reduc(term_type, s2)
        return Inf_res(args, tt)
    end
end

function infer_type_(term::EProd, ts_computed::Array{Inf_res})::Union{Inf_res,Error}
    # IDEA: This checking that all args are the same, really belongs to the DIAGONAL FUNCTOR of terms,
    # but this is a hodgepodge, so that's fine.
    # @assert length(term.data) == length(ts_computed) "$(length(term.data)) != $(length(ts_computed)) in $(term.data) != $(ts_computed)"
    # ^ i REALLY WANT to have this, except that HORRIBLE HACK in infer(TApp) passes an EMPTY EPROD here...
    if length(ts_computed) == 0 return Inf_res(Array{Type_}([]), TProd([])) end
    max_eargs_length = ts_computed .|> (x -> x.arg_types |> length) |> maximum
    if max_eargs_length > 0
        padded_args = [
            pad_elocs(ir.arg_types, arity(ir), max_eargs_length)
            for ir in ts_computed]
        ls = padded_args .|> length
        @assert ls[2:end] .|> (x -> x == ls[1]) |> all # CHECK that pad_elocs worked
        ts_computed = [Inf_res(newarg, ir.res_type) for (newarg, ir) in zip(padded_args, ts_computed)]
        #     return Inf_res(TProd(ts_computed .|> (x->x.res_type)))
    end
    # ^ Here, contravariance appears to imply that the subtyping you want is
    # the COMPILE-TIME SOLVABLE (universal) one, ie IF YOU HAVE MANY YOU CAN ALSO HAVE FEW-
    # as Opoosed to the MONO one (padding w/ dumb terms).

    # ^ In practice, this actually means there's ANOTHER WAY ( i think):
    # compute all the eargs_length's and do the pairwise robinsonUnify's in INCREASING (or is it Decreaing?) ORDER OF eargs_length,
    # so that you let robinsonUnify always pick the longest vector!!

    # IDEA: if max_eargs_length == 0, you STILL have to UNIFY the TLocs, which is currenty done by
    # JUST RUNNING robinsonUnify on the Empty prods, and using that behaviour.
    unified_RES_types = Array{Type_}([])
    last_one = pop!(ts_computed)
    for ir in ts_computed
        substs =  robinsonUnify(
            TProd(ir.arg_types), TProd(last_one.arg_types),
            ir |> arity, last_one |> arity)
        if substs isa Error
            return Error("ELocs typed $(ir.arg_types .|> pr) cannot be unified into ELocs typed $(last_one.arg_types .|> pr), with error '$(substs)'")
        end
        (s1, s2) = substs
        last_one = ass_reduc(last_one, s2)
        unified_RES_types::Array{Type_} = unified_RES_types .|> (x -> ass_reduc(x, s2)) # if they BECAME EQUAL to last_one, this should work
        push!(unified_RES_types, ass_reduc(ir.res_type, s1))
    end

    push!(unified_RES_types, last_one.res_type)
    return Inf_res(last_one.arg_types, TProd(unified_RES_types))
end

function infer_type_(term::EAbs, t_computed::Inf_res)::Union{Inf_res,Error}
    return Inf_res(Array{Type_}([]), TTerm(TProd(t_computed.arg_types), t_computed.res_type))
end
function infer_type_(term::ESumTerm, t_computed::Inf_res)::Union{Inf_res,Error}
    arT, tag = t_computed |> arity, term.tag
    types = vcat([TLoc(n) for n in (arT + 1):(arT + tag - 1)], [t_computed.res_type])
    return Inf_res(t_computed.arg_types, TForall(TSum(types)))
end
function infer_type_(term::EBranches, t_computed::Inf_res)::Union{Inf_res,Error}
    arT, tag = t_computed |> arity, term.tag
    types = vcat([TLoc(n) for n in (arT + 1):(arT + tag - 1)], [t_computed.res_type])
    return Inf_res(t_computed.arg_types, TForall(TSum(types)))
end

# function infer_type_(term::EBranches, ts_computed::Array{Inf_res})::Union{Inf_res, Error}



# Silly categorical-algebra-ish recursive wrapup:
function infer_type_rec(term::ELoc)::Union{Inf_res,Error} return infer_type_(term) end
function infer_type_rec(term::EGlob)::Union{Inf_res,Error} return infer_type_(term) end
function infer_type_rec(term::EUnit)::Union{Inf_res,Error} return infer_type_(term) end
function infer_type_rec(term::EAnno)::Union{Inf_res,Error}
    tt = infer_type_rec(term.expr)
    return (tt isa Error) ? tt : infer_type_(term, tt)
end
function infer_type_rec(term::EAbs)::Union{Inf_res,Error} tt = infer_type_rec(term.body); return (tt isa Error) ? tt : infer_type_(term, tt) end
function infer_type_rec(term::EProd)::Union{Inf_res,Error}
    tts::Array{Union{Inf_res,Error} } = infer_type_rec.(term.data)
    for tt in tts if tt isa Error return tt end end
    return infer_type_(term, Array{Inf_res}(tts))
end
function infer_type_rec(term::ESumTerm)::Union{Inf_res,Error} tt = infer_type_rec(term.data); return (tt isa Error) ? tt : infer_type_(term, tt) end
function infer_type_rec(term::EBranches)::Union{Inf_res,Error}
    tts = infer_type_rec.(term.ops_chances)
    for tt in tts if tt isa Error return tt end end
    return infer_type_(term, Array{Inf_res}(tts))
end
function infer_type_rec(term::EApp)::Union{Inf_res,Error}
    tts::Array{Union{Inf_res,Error}} = infer_type_rec.(term.ops_dot_ordered)
    for tt in tts if tt isa Error return tt end end
    return infer_type_(term, Array{Inf_res}(tts))
end




function infer_type_(term::EApp, ts_computed::Array{Inf_res})::Union{Inf_res,Error}
    # First, fix TLoc's by SQUASHING THEM TO BE TTERMS.
    # Idea: - EAbs come as TTErms (Inf_res with NO dependencies)  - ELocs come as InfRes WITH the dependency  - NONE of the inf_res have a Forall around cuz it's how it is in this mess
    ts_computed_2 = Array{Inf_res}([ts_computed[1]])
    for t in ts_computed[2:end]
        fake_tterm = TForall(TTerm(TLoc(1), TLoc(2)))
        tterm_subst = robinsonUnify(t.res_type, fake_tterm, t |> arity, fake_tterm.body |> arity)
        if tterm_subst isa Error return Error("Calling a non-function: $(t)")
        else push!(ts_computed_2, ass_reduc(t, tterm_subst[1]))
        end
    end
    # ^ Each of these still has ITS OWN TLoc's

    # Second, Unify the context of the TLocs:
    prod_w_unified_args = infer_type_(EProd([]), ts_computed_2)
    # ^ REUSING the TProd inference, HACKING the fact that Term is NOT used
    full_arity = prod_w_unified_args |> arity
    # ^Can i compute this in some smarter way?  # Dunno !
    ts_computed_res, args = Array{Type_}(prod_w_unified_args.res_type.data), TProd(prod_w_unified_args.arg_types)
    # ^ Switcharoo, TProd becomes array and array becomes TProd.. What a mess

    # Third, actually unify all in/outs:
    prev_out = ts_computed_res[1] # TODO fix when app is not a mess anymore
    for i in 2:length(ts_computed_res)
        next_in = ts_computed_res[i].t_in # YES this always exists now
        substs =  robinsonUnify(
            TForall(prev_out), TForall(next_in), full_arity, full_arity; unify_tlocs_ctx=false)
        # TODO: i DONT LIKE these Foralls, it's WRONG, but, it's the only way of accessing unify_tlocs_ctx atm
        if substs isa Error
            return Error("Mismatched app: get out type $(prev_out |> pr) but required type $(next_in |> pr), with error '$(substs)'")
        end
        (s1, s2) = substs
        # ^ Wait.. Are you telling me, if unify_tlocs_ctx=false, s1 and s2 are ALWAYS the same ???  # # Man, this is a crazy world..
        ts_computed_res = Array{Type_}(ts_computed_res .|> (x -> ass_reduc(x, s1)))
        # ^ the LENGTH of ts_computed_res DOES NOT CHANGE HERE
        # ^ Also Maybe you can SKIP updating all of them but who cares
        args = ass_reduc(args, s1) # Keep track of the Arg types, too
        full_arity = s1 |> arity
        prev_out = ts_computed_res[i].t_out
    end
    return Inf_res(args.data, ts_computed_res[end].t_out)
    # Returns the OUTPUT type instead of the composed TTerm type cuz this is a mess
end

