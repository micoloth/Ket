
# higher order typechecker using unification: Like unification.jl, but using my mylambda machinery

# from https://github.com/jozefg/higher-order-unification/


TOPFREE=100
newvar() = global TOPFREE = TOPFREE + 1

include("mylambda1.jl")

usesLocs(t::TGlob)::Array{Index} = Array{Index}([])
usesLocs(t::TLoc)::Array{Index} = Array{Index}([t.var])
usesLocs(t::TTop)::Array{Index} = Array{Index}([])
usesLocs(t::TApp)::Array{Index} = unique(vcat((t.ops_dot_ordered .|> usesLocs)...))
usesLocs(t::TProd)::Array{Index} = unique(vcat((t.data .|> usesLocs)...))
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

#>> I mean how does
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
Error=String
SimpRes = Union{Array{Constraint}, Error}

pr(c::Constraint)::String = pr(c.t1) *"=="*pr(c.t2)

function simplify_(t1::TApp, t2::TApp)::SimpRes
    @assert t1.ops_dot_ordered|>length ==2 && t2.ops_dot_ordered|>length==2  # TEMPORARY
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
    cons = DirectConstraint(t1.body, t2.body)
    # FOR NOW, these will be REALLY PICKY
    cons = simplify(cons)
    # Only accepted case: All constraints are about TLoc only and THE SAME
    is_same(c::Constraint) = (c.t1 isa TLoc) && (c.t1 == c.t2)
    if typeof(cons) == Error
        Error("Different lambdas: with this error: $(cons)")
    elseif length(cons) == 0 || (cons .|> is_same |> all)
        Array{Constraint}([]) 
    else 
        Error("Different lambdas $(pr(t1)) != $(pr(t2)): I know I'm being picky, but impossible to simplify this part: $(cons)")
    end
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

function simplify_(t1::Type_, t2::Type_)::SimpRes # base case
    if t1 == t2 Array{Constraint}([])
    elseif typeof(t1) === TLoc || typeof(t2) === TLoc Array{Constraint}([DirectConstraint(t1, t2)]) 
    else Error("Different: $(pr(t1)) is really different from $(pr(t2))")
    end
end

swap(c::DirectConstraint) = ReverseConstraint(c.t2, c.t1)
swap(c::ReverseConstraint) = DirectConstraint(c.t2, c.t1)
simplify_(c::DirectConstraint)::SimpRes = simplify_(c.t1, c.t2)
function simplify_(c::ReverseConstraint)::SimpRes 
    res = simplify_(c.t2, c.t1)
    (res isa Error) ? res : (Array{Constraint}(res .|> swap))
end


function backtrack(array::SimpRes)::SimpRes
    if typeof(array) === Error
        return array
    end
    reduced = Set{Constraint}([])
    while length(array) > 0
        array2 = Array{Constraint}([])
        for c in array
            cs = simplify_(c)
            if typeof(cs) === Error return cs
            elseif length(cs)==1 && cs[1]==c push!(reduced, c) 
            elseif length(cs)!=0 append!(array2, cs) end
        end
        array = array2    
    end
    return Array{Constraint}([reduced...])
end

function simplify(t1::Type_, t2::Type_)::SimpRes  # simply the toplevel interface
    t1=reduc(t1)
    t2 = reduc(t2)
    return backtrack(Array{Constraint}([DirectConstraint(t1, t2)]))
    # array=[Constraint(t1, t2)]
end

simplify(c::Constraint)::SimpRes = simplify(c.t1, c.t2)



# Unify: solve f(x) = g(y) in the sense of finding x AND y,
# EXCEPT it WONT fail if post-applying some DROPPINGs here and there will help.
# It WONT RETURN THEM, either. See above.

Subst = Dict{Index, Type_}  # I'm using this as a SPARSE VECTOR

# idea: in NO CASE x=f(x) can be solved, (if types_ are REDUCED), because we handle RecursiveTypes Differently!!
function robinson_check_not_recursive(tloc::TLoc, tt::Type_, subst::Subst)::Bool
    STACK = Array{Type_}([tt])
    while (length(STACK) > 0)
        println("Happing!")
        t = pop!(STACK)
        for v in usesLocs(t)
            if tloc.var == v return false
            elseif v in keys(subst)
                push!(STACK, subst[v])
            end
        end
    end
    # for v in usesLocs(tt)
    #     if tloc.var == v return false end
    # end
    return true
end


get_reduc_subst(t::Array{TProd}) = TApp(vcat([t[end]], t[end-1:-1:1] .|> (x->TForall(x))))
get_reduc_subst(t::Array{Type_}) = TApp(vcat([t[end]], t[end-1:-1:1] .|> (x->TForall(x))))
# IMPORTANT: ALL EXCEPT (potentially) the >FIRST< should be TPRODS !!!!!

# ASSOCIATIVE OPERATION to compose the above:
ass_smart_reduc(t...) = (length(t) <= 1) ? (collect(t)) : ([get_reduc_subst(collect(t)) |> reduc]) 
# TODO: change "[reduc()]" in "smart_reduc" !!
ass_reduc(t::TProd ...)::TProd = (length(t) == 1) ? (t[1]) : (get_reduc_subst(collect(t)) |> reduc) 
ass_reduc(t1::Type_, ts::TProd ...)::Type_ = (length(ts) == 0) ? (t1) : (get_reduc_subst(vcat([t1], collect(ts))) |> reduc) 


function get_subst_prod(tloc::TLoc, tt::Type_, current_arity::Int)::TProd
    # resulting_arity = current_arity - 1
    # you have ALREADY TESTED that tt does not contain tloc, that's the whole point !!!!
    prod = vcat(
        Array{Type_}([TLoc(i) for i in 1:(tloc.var-1)]),
        Array{Type_}([TLoc(0)]), # Placeholder, complete nonsense, it's getting replaced
        Array{Type_}([TLoc(i) for i in (tloc.var:current_arity-1)])        
    )
    prod[tloc.var] = get_reduc_subst(Array{Type_}([tt, TProd(prod)])) |> reduc
    TProd(prod)
end


function robinsonUnify(t1::TForall, t2::TForall, t1arity::Index, t2arity::Index)::Union{Tuple{TProd, TProd}, Error}
    # Dumb, i promise i'll make this better:

    # Not gonna lie, i Did like this a lot...
    # new_shared = newval(c.t1.var, shared_locs)
    # shared_locs[new_shared] = UsedReferences([c.t1.var], [c.t2.var], [], [])
    # s1[c.t1.var] = TLoc(new_shared)
    
    # IDEA: The following s1 and s2 are ALSO used in a case where t1 and t2 contain EMPTY PROD, in which case they are returned (see below) but EVERYTHING works. 
    # >>STILL, you might want to create a different function..
    s1 = TProd([TLoc(i) for i in 1:t1arity])
    t1 = TApp([s1, t1])
    s2 = TProd([TLoc(i) for i in (t1arity+1):(t1arity+t2arity)])
    t2 = TApp([s2, t2])
    middle_subst = Subst()
    # Now everything is Shared # Note that the below Reduces:
    cs = simplify(t1, t2) # they are Already bodies, at this point
    if cs isa Error return cs end
    STACK = cs
    while (length(STACK) > 0)
        c = pop!(STACK)
        ct1, ct2 = c.t1, c.t2
        while (ct1 isa TLoc && ct1.var in keys(middle_subst)) ct1 = middle_subst[ct1.var] end
        while (ct2 isa TLoc && ct2.var in keys(middle_subst)) ct2 = middle_subst[ct2.var] end

        if ct1 isa TLoc && ct2 isa TLoc
            middle_subst[ct1.var] = ct2 # it's ARBITRARY since these names have no meaning anyway
        elseif ct1 isa TLoc
            if !robinson_check_not_recursive(ct1, ct2, middle_subst) return Error("$(ct1) == $(ct2) is not a thing (recursive)") end
            middle_subst[ct1.var] = ct2
        elseif ct2 isa TLoc
            if !robinson_check_not_recursive(ct2, ct1, middle_subst) return Error("$(ct2) == $(ct1) is not a thing (recursive)") end
            middle_subst[ct2.var] = ct1
        else
            cs_inside = simplify(ct1, ct2)
            if cs_inside isa Error return cs_inside end
            append!(STACK, cs_inside)
        end
    end

    current_total_subst =  Array{TProd}([]) # SMART_REDUCED VERSION # (Can be a single [TProd] or the whole list)
    # ^ Still, to pass into get_reduc_subst IN THIS ORDER
    current_arity = t1arity + t2arity
    for (i, tt) in middle_subst
        tt_updated = ass_reduc(tt, current_total_subst...)
        i_updated = ass_reduc(TLoc(i), current_total_subst...)
        new_subst = get_subst_prod(i_updated, tt_updated, current_arity)
        
        current_total_subst::Array{TProd} = ass_smart_reduc(current_total_subst..., new_subst)
        current_arity = arity(current_total_subst[end]) # The beauty of this is this is Enough... I HOPE LOL
    end
    if length(current_total_subst) == 0
        # @assert (t1arity == t2arity) "$(t1arity) != $(t2arity), HOW tho ..."
        # ^ This assert makes sense EVERY TIME THERE'S NO PASSED ARITIES
        # TODO: remove this dumb shit, replace with LITERALLY NOTHING
        return s1, s2
    end
    
    final_subst = ass_reduc(current_total_subst...)
    subst1 = TProd(final_subst.data[1:t1arity])
    subst2 = TProd(final_subst.data[(t1arity+1):(t1arity+t2arity)])
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





function test_unify(t1, t2)
    println("Unify ", t1|> pr, "  and  ", t2|> pr, ":")
    (s1, s2) = robinsonUnify(TForall(t1), TForall(t2))
    red1 = reduc(TApp([s1, TForall(t1)])) 
    println("reduced term: ", red1 |> pr)
    res = (red1 == reduc(TApp([s2, TForall(t2)])))
    println(res)
    return res
end

t1 = TAppAuto(TGlob("G0"), TLoc(1))
t2 = TAppAuto(TGlob("G0"), TLoc(2))
simplify(t1, t2) == [DirectConstraint(TLoc(1), TLoc(2))]
robinsonUnify(TForall(t1), TForall(t2))
@assert test_unify(t1, t2)

t1 = TAppAuto(TGlob("G0"), TLoc(1))
t2 = TAppAuto(TGlob("G0"), TGlob("G99"))
c = simplify(t1, t2) == [DirectConstraint(TLoc(1), TGlob("G99"))]
robinsonUnify(TForall(t1), TForall(t2))
@assert test_unify(t1, t2)

t1 = TAppAuto(TForall(TLoc(1)), TLoc(1))
t2 = TLoc(2)
simplify(t1, t2) == [DirectConstraint(TLoc(1), TLoc(2))]
robinsonUnify(TForall(t1), TForall(t2))
@assert test_unify(t1, t2)

t1 = TForall(TLoc(1))
t2 = TForall(TLoc(1))
simplify(t1, t2) == []
robinsonUnify(TForall(t1), TForall(t2))
@assert test_unify(t1, t2)

t1 = TForall(TLoc(1))
t2 = TForall(TLoc(2))
simplify(t1, t2) isa Error
robinsonUnify(TForall(t1), TForall(t2))
@assert robinsonUnify(TForall(t1), TForall(t2)) isa Error

t1 = TForall(TLoc(1))
t2 = TLoc(3)
simplify(t1, t2) == [DirectConstraint(TForall(TLoc(1)), TLoc(3))]
robinsonUnify(TForall(t1), TForall(t2))
@assert test_unify(t1, t2)

t1 = TForall(TLoc(1))
t2 = TGlob("G")
simplify(t1, t2) == Error("Different: ∀(T1) is really different from G")
robinsonUnify(TForall(t1), TForall(t2))
@assert robinsonUnify(TForall(t1), TForall(t2)) isa Error

t1 = TForall(TLoc(1))
t2 = TForall(TLoc(1))
simplify(t1, t2)
robinsonUnify(TForall(t1), TForall(t2))
@assert test_unify(t1, t2)

t = TAppAuto(TForall(TLoc(1)), TGlob("G1"))
t1 = TAppAuto(TLoc(3), t)
t2 = TAppAuto(TLoc(4), t)
simplify(t1, t2) == [DirectConstraint(TLoc(3), TLoc(4))]
robinsonUnify(TForall(t1), TForall(t2))
@assert test_unify(t1, t2)

t1 = TAppAuto(TGlob("G2"), TLoc(3))
t2 = TAppAuto(TGlob("G2"), TForall(TAppAuto(TLoc(1), TGlob("G3"))))
repr(simplify(t1, t2)) == repr([DirectConstraint(TLoc(3), TForall(TApp([TProd([TGlob("G3")]), TLoc(1)])))])
# ^ Go fuck yourself, then die 
robinsonUnify(TForall(t1), TForall(t2))
@assert test_unify(t1, t2)

t1 = TAppAuto(TGlob("G2"), TGlob("G3"))
t2 = TAppAuto(TGlob("G2"), TForall(TAppAuto(TLoc(1), TGlob("G3"))))
simplify(t1, t2)  == Error("Different: T3 is really different from ∀([Just (T3).(T1)])")  # Globals cannot be "solved", and that's ok
robinsonUnify(TForall(t1), TForall(t2))
@assert robinsonUnify(TForall(t1), TForall(t2)) isa Error

t1 = TForall(TAppAuto(TGlob("F"), TLoc(1)))   
t2 = TForall(TAppAuto(TGlob("F"), TLoc(2)))   
simplify(t1, t2) isa Error  # LAMBDAS CANNOT BE UNIFIED (below, they are preapplied, which is a whole different discussion!!!)
robinsonUnify(TForall(t1), TForall(t2))
@assert robinsonUnify(TForall(t1), TForall(t2)) isa Error

t1 = TApp([TProd([TGlob("X"), TGlob("Y")]), TForall(TAppAuto(TGlob("F"), TLoc(1)))])
t2 = TApp([TProd([TGlob("Y"), TGlob("X")]), TForall(TAppAuto(TGlob("F"), TLoc(2)))])
simplify(t1, t2) == DirectConstraint[]
robinsonUnify(TForall(t1), TForall(t2))
@assert test_unify(t1, t2)

t1 = TApp([TProd([TGlob("X"), TGlob("Y")]), TForall(TAppAuto(TGlob("F"), TLoc(1)))])
t2 = TApp([TProd([TGlob("X"), TGlob("Y")]), TForall(TAppAuto(TGlob("F"), TLoc(2)))])
simplify(t1, t2) == Error("Different: X is really different from Y")
robinsonUnify(TForall(t1), TForall(t2))
@assert robinsonUnify(TForall(t1), TForall(t2)) isa Error

t1 = TApp([TProd([TLoc(3), TLoc(2)]), TForall(TAppAuto(TGlob("F"), TLoc(1)))])
t2 = TApp([TProd([TLoc(1), TLoc(4)]), TForall(TAppAuto(TGlob("F"), TLoc(2)))])
simplify(t1, t2) == [DirectConstraint(TLoc(3), TLoc(4))]
robinsonUnify(TForall(t1), TForall(t2))
@assert test_unify(t1, t2)

t1 = TApp([TProd([TGlob("X"), TLoc(2)]), TForall(TAppAuto(TLoc(2), TLoc(1)))])
t2 = TApp([TProd([TLoc(1), TLoc(4)]), TForall(TAppAuto(TGlob("F"), TLoc(2)))])
simplify(t1, t2)  == [DirectConstraint(TGlob("X"), TLoc(4)), DirectConstraint(TLoc(2), TGlob("F"))]
robinsonUnify(TForall(t1), TForall(t2))
@assert test_unify(t1, t2)

t1 = TAppAuto(TLoc(4), TGlob("X"))
t2 = TAppAuto(TTermAuto(TLoc(1), TLoc(2)), TLoc(3)) 
repr(simplify(t1, t2)) == repr([DirectConstraint(TLoc(4), TTerm(TLoc(1), TLoc(2))), DirectConstraint(TGlob("X"), TLoc(3))])
# ^ Go fuck yourself, then die 
robinsonUnify(TForall(t1), TForall(t2))
@assert test_unify(t1, t2)

t1 = TProd([TLoc(1), TLoc(2)])
t2 = TProd([TLoc(3), TLoc(3)])
simplify(t1, t2)
robinsonUnify(TForall(t1), TForall(t2))
@assert test_unify(t1, t2)

t1 = TProd([TLoc(1), TLoc(1)])
t2 = TProd([TGlob("F"), TGlob("G")]) #OUCHHHH
simplify(t1, t2) == [DirectConstraint(TLoc(1), TGlob("G")), DirectConstraint(TLoc(1), TGlob("F"))]
robinsonUnify(TForall(t1), TForall(t2)) # Error, nice
@assert robinsonUnify(TForall(t1), TForall(t2)) isa Error

t1 = TProd([TLoc(1), TGlob("F")])
t2 = TProd([TGlob("G"), TLoc(1)]) #otoh, this SHOULD keep working..
simplify(t1, t2) == [DirectConstraint(TLoc(1), TGlob("G")), DirectConstraint(TGlob("F"), TLoc(1))]
robinsonUnify(TForall(t1), TForall(t2))
@assert test_unify(t1, t2)

t1 = TProd([TLoc(1), TLoc(1)])
t2 = TProd([TLoc(1), TTermAuto(TGlob("A"), TLoc(1))])
repr(simplify(t1, t2)) == repr([DirectConstraint(TLoc(1), TLoc(1)), DirectConstraint(TLoc(1), TTermAuto(TGlob("A"), TLoc(1)))])
robinsonUnify(TForall(t1), TForall(t2)) # Recursive Error, nice!
@assert robinsonUnify(TForall(t1), TForall(t2)) isa Error

t1 = TProd([TLoc(1), TLoc(1), TLoc(2), TLoc(2)])
t2 = TProd([TLoc(1), TLoc(2), TLoc(2), TTermAuto(TGlob("A"), TTermAuto(TGlob("B"), TLoc(1)))])
repr(simplify(t1, t2)) == repr([DirectConstraint(TLoc(2), TTermAuto(TGlob("A"), TTermAuto(TGlob("B"), TLoc(1)))), DirectConstraint(TLoc(1), TLoc(1)), DirectConstraint(TLoc(2), TLoc(2)), DirectConstraint(TLoc(1), TLoc(2))])
robinsonUnify(TForall(t1), TForall(t2)) # Recursive Error, nice!
@assert robinsonUnify(TForall(t1), TForall(t2)) isa Error

t1 = TProd([TLoc(1), TLoc(1), TLoc(2), TLoc(2)])
t2 = TProd([TTermAuto(TGlob("A"), TTermAuto(TGlob("B"), TGlob("C"))), TLoc(2), TLoc(2), TTermAuto(TGlob("A"), TTermAuto(TGlob("B"), TLoc(1)))])
repr(Set(simplify(t1, t2))) == repr(Set(DirectConstraint[DirectConstraint(TLoc(2), TLoc(2)), DirectConstraint(TLoc(1), TTermAuto(TGlob("A"), TTermAuto(TGlob("B"), TGlob("C")))), DirectConstraint(TLoc(2), TTermAuto(TGlob("A"), TTermAuto(TGlob("B"), TLoc(1)))), DirectConstraint(TLoc(1), TLoc(2))]))
robinsonUnify(TForall(t1), TForall(t2)) .|> pr
@assert test_unify(t1, t2)   #####  YESSSSS

t1 = TProd([TLoc(1), TLoc(2)])
t2 = TProd([TLoc(2), TTermAuto(TGlob("A"), TLoc(1))])
repr(simplify(t1, t2)) == "DirectConstraint[DirectConstraint(TLoc(2), TTermAuto(TGlob(\"A\"), TLoc(1))), DirectConstraint(TLoc(1), TLoc(2))]"
robinsonUnify(TForall(t1), TForall(t2))
@assert test_unify(t1, t2)

t1 = TProd([TLoc(1), TLoc(1), TLoc(2), TLoc(2)])
t2 = TProd([TGlob("F"), TLoc(3), TLoc(3), TGlob("G")])
simplify(t1, t2) == [DirectConstraint(TLoc(2), TGlob("G")), DirectConstraint(TLoc(1), TLoc(3)), DirectConstraint(TLoc(1), TGlob("F")), DirectConstraint(TLoc(2), TLoc(3))]
robinsonUnify(TForall(t1), TForall(t2)) # Error, nice
@assert robinsonUnify(TForall(t1), TForall(t2)) isa Error

t1 = TForall(TGlob("A"))
t2 =  TGlob("A")
simplify(t1, t2) # Nope, and that's fine
robinsonUnify(t1, t2)
@assert robinsonUnify(TForall(t1), TForall(t2)) isa Error

t1 = TProd([TLoc(1), TLoc(1), TLoc(2), TLoc(2)])
t2 = TProd([TGlob("F"), TLoc(1), TLoc(1), TGlob("G")])
simplify(t1, t2) == [DirectConstraint(TLoc(2), TLoc(1)), DirectConstraint(TLoc(1), TLoc(1)), DirectConstraint(TLoc(2), TGlob("G")), DirectConstraint(TLoc(1), TGlob("F")), ]
robinsonUnify(TForall(t1), TForall(t2)) # Error, nice
@assert robinsonUnify(TForall(t1), TForall(t2)) isa Error

t1, t2 = TLoc(3), TForall(TTermAuto(TGlob("A"), TLoc(2)))
@assert test_unify(t1, t2.body)

t1 = TForall(TTermAuto(TLoc(1), TProd([TGlob("A"), TLoc(2)])))
t2 = TForall(TTermAuto(TLoc(1), TLoc(2)))
s1, s2 = robinsonUnify(t1, t2)
@assert test_unify(t1.body, t2.body)

t1 = TForall(TLoc(3))
t2 = TForall(TTermAuto(TLoc(1), TLoc(2)))
s1, s2 = robinsonUnify(t1, t2)
@assert test_unify(t1.body, t2.body)

# function prepTransEx(l, g1, g2)
#     v1=vcat([[TLoc(i), TLoc(i)] for i in 1:l]...)
#     v2=vcat([[TLoc(i), TLoc(i)] for i in 1:l-1]...)
#     TProd(v1), TProd(vcat([TGlob(g1)], v2, [TGlob(g2)]))
# end
# t1, t2 = prepTransEx(505, "F", "F")
# robinsonUnify(TForall(t1), TForall(t2))
# @assert test_unify(t1, t2)

# t1, t2 = prepTransEx(10, "F", "G")
# robinsonUnify(TForall(t1), TForall(t2))



# K for TESTS w/ DIFFERENT NUMBER OF ITEMS NOW:
t1 = TProd([TLoc(1), TGlob("B")])
t2 = TProd([TGlob("A"), TLoc(1), TLoc(2)])
@assert robinsonUnify(t1, t2) isa Error

t1 = TProd([TLoc(1), TGlob("B"), TLoc(2)])
t2 = TProd([TGlob("A"), TLoc(1)])
s1, s2 = robinsonUnify(t1, t2)
ass_reduc(t1, s1) |> pr
ass_reduc(t2, s2) |> pr


t1 = TProd([TGlob("A"), TGlob("B")])
t2 = TProd([TGlob("A"), TGlob("B")])
@assert robinsonUnify(t1, t2) == (TProd(Type_[]), TProd(Type_[]))

t1 = TProd([TGlob("A"), TGlob("B"), TGlob("C")])
t2 = TProd([TGlob("A"), TGlob("B")])
@assert robinsonUnify(t1, t2) == (TProd(Type_[]), TProd(Type_[]))

t1 = TTerm(TProd([TLoc(1), TGlob("B"), TLoc(2)]), TGlob("Z"))
t2 = TTerm(TProd([TGlob("A"), TLoc(1)]), TGlob("Z"))
@assert robinsonUnify(t1, t2) isa Error

t1 = TTerm(TProd([TLoc(1), TGlob("B")]), TGlob("Z"))
t2 = TTerm(TProd([TGlob("A"), TLoc(1), TLoc(2)]), TGlob("Z"))
s1, s2 = robinsonUnify(t1, t2)
ass_reduc(t1, s1) |> pr
ass_reduc(t2, s2) |> pr


t1 = TTermAuto(TTerm(TProd([TLoc(1), TLoc(2)]), TGlob("Z")), TGlob("Z"))
t2 = TTermAuto(TTerm(TProd([TGlob("A"), TLoc(2)]), TGlob("Z")), TGlob("Z"))
@assert test_unify(t1, t2)

t1 = TTermAuto(TTerm(TProd([TLoc(1)]), TGlob("Z")), TGlob("Z"))
t2 = TTermAuto(TTerm(TProd([TGlob("A"), TLoc(2)]), TGlob("Z")), TGlob("Z"))
@assert robinsonUnify(t1, t2) isa Error

t1 = TTermAuto(TTerm(TProd([TLoc(1), TLoc(2)]), TGlob("Z")), TGlob("Z"))
t2 = TTermAuto(TTerm(TProd([TGlob("A")]), TGlob("Z")), TGlob("Z"))
t1 |> pr
t2 |> pr
s1, s2 = robinsonUnify(t1, t2)
ass_reduc(t1, s1) |> pr
ass_reduc(t2, s2) |> pr


sr = ass_reduc

# Each TLoc refers to position in the row BELOW:
t1 = TProd([TTerm(TLoc(1), TLoc(2)), TLoc(3)])
t2 = TProd([TLoc(1), TLoc(2), TLoc(2)])
t3 = TProd([TGlob("G"), TLoc(1)])
t4 = TProd([TTermAuto(TGlob("A"), TGlob("B"))])
get_reduc_subst([t1, t2, t3, t4]) |> reduc |> pr == "[G->A->B x A->B]"

sr(sr(t1, t2), sr(t3, t4)) |> pr
sr(sr(t1, t2, t3), t4) |> pr
sr(t1, sr(t2, t3, t4)) |> pr



# Each TLoc refers to position in the row BELOW:
t1 = TProd([TLoc(1), TLoc(2), TLoc(3), TLoc(4), TLoc(5)])
t2 = TProd([TLoc(1), TLoc(1), TLoc(2), TLoc(3), TLoc(4)])
t3 = TProd([TLoc(1), TLoc(2), TLoc(3), TLoc(3)])
t4 = TProd([TLoc(1), TLoc(2), TLoc(2)])
t5 = TProd([TLoc(4), TGlob("A")])
get_reduc_subst([t1, t2, t3, t4, t5]) |> reduc |> pr == "[T4 x T4 x A x A x A]"

sr(sr(t1, t2), sr(t3, t4, t5)) |> pr
sr(sr(t1, t2, t3, t4), t5) |> pr
sr(t1, sr(t2, t3), sr(t4, t5)) |> pr



# Each TLoc refers to position in the row BELOW:
t1 = TProd([TLoc(1), TGlob("F"), TLoc(3), TTerm(TProd([TLoc(4)]), TLoc(5))])
t2 = TProd([TLoc(1), TGlob("SKIPPED"), TTerm(TLoc(2), TLoc(3)), TLoc(1), TLoc(1)])
t3 = TProd([TLoc(2), TLoc(1), TLoc(2)])
t4 = TProd([TLoc(1), TTerm(TProd([TLoc(2)]), TLoc(3))])
t5 = TProd([TLoc(2), TGlob("Z"), TGlob("Z")])
get_reduc_subst([t1, t2, t3, t4, t5]) |> reduc |> pr == "[Z->Z x F x T2->Z->Z x Z->Z->Z->Z]"

sr(sr(t1, t2), sr(t3, t4, t5)) |> pr
sr(sr(t1, t2, t3, t4), t5) |> pr
sr(t1, sr(t2, t3), sr(t4, t5)) |> pr

struct Inf_res
    # IDEA: you can ALWAYS turn this into a TTerm !
    # Other idea: this is always BARE, ie with NO Forall around. This is because it should be around BOTHthe args and the res!
    arg_types::Array{Type_} # IDEA: you can always turn this into a TProd
    res_type::Type_
end
Inf_res(res_type::Type_) = Inf_res([], res_type)
Base.:(==)(a::Inf_res, b::Inf_res) = Base.:(==)(a.arg_types, b.arg_types) && Base.:(==)(a.res_type, b.res_type)
ass_reduc(ir::Inf_res, t::TProd ...) = Inf_res(ass_reduc(TProd(ir.arg_types), t...).data, ass_reduc(ir.res_type, t...))
arity(ir::Inf_res) = max(
    (length(ir.arg_types)> 0) ? (ir.arg_types .|> arity |> maximum) : 0, # Yee! Dynamic typing!!
    ir.res_type |> arity)
pad_elocs(elocs::Array{Type_}, max_t_arity::Int, max_length::Int)::Array{Type_} = vcat(elocs, [TLoc(i + max_t_arity) for i in 1:(max_length - length(elocs))])

function infer_type_(term::ELoc)::Union{Inf_res, Error} 
    return Inf_res(
        Array{Type_}([TLoc(i) for i in 1:term.n]),
        # TForall(TLoc(term.n))
        TLoc(term.n)
    )
end

function infer_type_(term::EGlob)::Union{Inf_res, Error} 
    if term.type isa TForall return Inf_res(term.type.body) 
    # ^ This is because Inf_res's are Naked (no Forall) for some reason- BOY will this become a mess
    else return Inf_res(term.type) end
end
function infer_type_(term::EUnit)::Union{Inf_res, Error} return Inf_res(TTop()) end
function infer_type_(term::EAnno, t_computed::Inf_res)::Union{Inf_res, Error} 
    substs = robinsonUnify(t_computed.res_type, term.type)
    if substs isa Error return substs end
    s1, s2 = substs
    if t_computed.arg_types |> length == 0 # HOPEFULLY this is a Type, NOT a body
        if length(s2.data) == 0  # HACK HACK: Should TForall be there or not? :(
            return Inf_res(term.type)
        else
            return Inf_res(ass_reduc(term.type.body, s2))
        end
    else  # HACK HACK HACK: Workaround for the fact that if one writes "ELoc(1):A", it's CLEAR what he means, EVEN if ELoc(1) is a PROJ FUNCTION, NOT a term
        return ass_reduc(t_computed, s1)
    end
end

function infer_type_(term::EProd, ts_computed::Array{Inf_res})::Union{Inf_res, Error} 
    # IDEA: This checking that all args are the same, really belongs to the DIAGONAL FUNCTOR of terms, 
    # but this is a hodgepodge, so that's fine.
    max_eargs_length = ts_computed .|> (x->x.arg_types |> length) |> maximum
    if max_eargs_length > 0
        padded_args = [
            pad_elocs(ir.arg_types, arity(ir), max_eargs_length)
            for ir in ts_computed]
        ls = padded_args .|> length
        @assert ls[2:end] .|> (x->x==ls[1]) |> all # CHECK that pad_elocs worked
        ts_computed = [Inf_res(newarg, ir.res_type) for (newarg, ir) in zip(padded_args, ts_computed)]
        #     return Inf_res(TProd(ts_computed .|> (x->x.res_type))) 
    end
    # ^ Here, contravariance appears to imply that the subtyping you want is
    # the COMPILE-TIME SOLVABLE (universal) one, ie IF YOU HAVE MANY YOU CAN ALSO HAVE FEW- 
    # as Opoosed to the MONO one (padding w/ dumb terms).
    
    # IDEA: if max_eargs_length == 0, you STILL have to UNIFY the TLocs, which is currenty done by
    # JUST RUNNING robinsonUnify on the Empty prods, and using that behaviour.    
    unified_RES_types = Array{Type_}([])
    last_one = pop!(ts_computed)
    for ir in ts_computed
        substs =  robinsonUnify(
            TProd(ir.arg_types), TProd(last_one.arg_types),
            ir |> arity, last_one |> arity)
        if substs isa Error 
            return Error("ELocs typed $(ir.arg_types .|> pr) cannot be unified with ELocs typed $(last_one.arg_types .|> pr), with error '$(substs)'")
        end
        (s1, s2) = substs
        last_one = ass_reduc(last_one, s2)
        unified_RES_types = unified_RES_types .|> (x->ass_reduc(x, s2)) # if they BECAME EQUAL to last_one, this should work
        push!(unified_RES_types, ass_reduc(ir.res_type, s1))
    end 

    push!(unified_RES_types, last_one.res_type)
    return Inf_res(last_one.arg_types, TProd(unified_RES_types))
end

function infer_type_(term::EAbs, t_computed::Inf_res)::Union{Inf_res, Error} 
    return Inf_res(Array{Type_}([]), TTerm(TProd(t_computed.arg_types), t_computed.res_type))
end
function infer_type_(term::ESumTerm, t_computed::Inf_res)::Union{Inf_res, Error} 
    arT, tag, tot = t_computed |> arity, term.tag, term.total_branches
    types = vcat([TLoc(n) for n in (arT+1):(arT+tag-1)], [t_computed.res_type], [TLoc(n) for n in (tag+arT):(arT+tot-1)])
    return Inf_res(t_computed.arg_types, TForall(TSum(types)))
end

# function infer_type_(term::EBranches, ts_computed::Array{Inf_res})::Union{Inf_res, Error} 



# Silly categorical-algebra-ish recursive wrapup:
function infer_type_rec(term::ELoc)::Union{Inf_res, Error} return infer_type_(term) end
function infer_type_rec(term::EGlob)::Union{Inf_res, Error} return infer_type_(term) end
function infer_type_rec(term::EUnit)::Union{Inf_res, Error} return infer_type_(term) end
function infer_type_rec(term::EAnno)::Union{Inf_res, Error} tt = infer_type_rec(term.expr); return (tt isa Error) ? tt : infer_type_(term, tt) end
function infer_type_rec(term::EAbs)::Union{Inf_res, Error} tt = infer_type_rec(term.body); return (tt isa Error) ? tt : infer_type_(term, tt) end
function infer_type_rec(term::EProd)::Union{Inf_res, Error} 
    tts = term.data .|> infer_type_rec
    for tt in tts if tt isa Error return tt end end
    return infer_type_(term, tts) 
end
function infer_type_rec(term::ESumTerm)::Union{Inf_res, Error} tt = infer_type_rec(term.data); return (tt isa Error) ? tt : infer_type_(term, tt) end
function infer_type_rec(term::EBranches)::Union{Inf_res, Error} 
    tts = term.ops_chances .|> infer_type_rec
    for tt in tts if tt isa Error return tt end end
    return infer_type_(term, tts) 
end
function infer_type_rec(term::EApp)::Union{Inf_res, Error} 
    tts = term.ops_dot_ordered .|> infer_type_rec
    for tt in tts if tt isa Error return tt end end
    return infer_type_(term, tts) 
end

e = ELoc(2)
@assert infer_type_rec(e) == Inf_res(Type_[TLoc(1), TLoc(2)], TLoc(2))

e = EGlob("f", TTermAuto(TGlob("A"), TGlob("B")))
@assert infer_type_rec(e) == Inf_res(Type_[], TTermAuto(TGlob("A"), TGlob("B")))

e = EAnno(ELoc(1), TGlob("A"))
@assert infer_type_rec(e) == Inf_res(Type_[TGlob("A")], TGlob("A"))

e = EAnno(ELoc(2), TGlob("A"))
@assert infer_type_rec(e) == Inf_res(Type_[TLoc(1), TGlob("A")], TGlob("A"))

tglob = TForall(TTermAuto(TGlob("A"), TLoc(2)))
tanno = TForall(TTermAuto(TLoc(1), TGlob("B")))
# tanno = TForall(TTermAuto(TGlob("A"), TGlob("B")))
# tanno = TTermAuto(TGlob("A"), TGlob("B"))
e = EAnno(EGlob("f", tglob), tanno)
@assert infer_type_rec(e) == Inf_res(Type_[], TTermAuto(TGlob("A"), TGlob("B")))


tt = TTermAuto(TGlob("A"), TGlob("B"))
e = EProd([EGlob("f", tt), EGlob("g", tt)])
@assert infer_type_rec(e) == Inf_res(Type_[], TProd(Type_[TTermAuto(TGlob("A"), TGlob("B")), TTermAuto(TGlob("A"), TGlob("B"))]))

tt = TForall(TTermAuto(TLoc(1), TGlob("B")))
e = EProd([EGlob("f", tt), EGlob("g", tt)])
@assert infer_type_rec(e).res_type |> pr == "[T1->B x T2->B]" # T2, important! GOOD

e = EProd([ELoc(2), ELoc(2)])
@assert infer_type_rec(e) == Inf_res(Type_[TLoc(1), TLoc(2)], TProd(Type_[TLoc(2), TLoc(2)]))

e = EProd([ELoc(2), EAnno(ELoc(2), TLoc(4))])
@assert infer_type_rec(e) == Inf_res(Type_[TLoc(1), TLoc(5)], TProd(Type_[TLoc(5), TLoc(5)]))


e = EProd([EAnno(ELoc(1), TLoc(3)), EAnno(ELoc(1), TLoc(4))])
@assert infer_type_rec(e) == Inf_res(Type_[TLoc(6)], TProd(Type_[TLoc(6), TLoc(6)]))


e = EProd([EAnno(ELoc(1), TLoc(3)), EAnno(ELoc(1), TLoc(4)), EAnno(ELoc(2), TLoc(5))])
@assert infer_type_rec(e) == Inf_res(Type_[TLoc(6), TLoc(11)], TProd(Type_[TLoc(6), TLoc(6), TLoc(11)]))

e = EAbs(EProd([ELoc(2), EAnno(ELoc(1), TGlob("T"))]))
@assert infer_type_rec(e) == Inf_res(Type_[], TTerm(TProd(Type_[TGlob("T"), TLoc(1)]), TProd(Type_[TLoc(1), TGlob("T")])))

e = EProd([EAnno(ELoc(1), TLoc(2)), EAnno(ELoc(1), TLoc(3)), EAnno(ELoc(1), TLoc(4))])
@assert infer_type_rec(e) == Inf_res(Type_[TLoc(7)], TProd(Type_[TLoc(7), TLoc(7), TLoc(7)]))

e = EAnno(EAbs(EGlob("b", TGlob("B"))), TTermAuto(TProd([TGlob("A")]),  TGlob("B")))
infer_type_rec(e).res_type |> pr
@assert infer_type_rec(e) == Inf_res(Type_[], TTerm(TProd(Type_[TProd(Type_[TGlob("A")])]), TGlob("B")))





function infer_type_(term::EApp, ts_computed::Array{Inf_res})::Union{Inf_res, Error} 
    # First, fix TLoc's by SQUASHING THEM TO BE TTERMS. 
    # Idea: - EAbs come as TTErms (Inf_res with NO dependencies)  - ELocs come as InfRes WITH the dependency  - NONE of the inf_res have a Forall around cuz it's how it is in this mess
    ts_computed_2 = Array{Inf_res}([ts_computed[1]])
    for t in ts_computed[2:end]
        fake_tterm = TForall(TTerm(TLoc(1), TLoc(2)))
        tterm_subst = robinsonUnify(t.res_type, fake_tterm, t|>arity, fake_tterm.body |> arity)
        if tterm_subst isa Error return Error("Calling a non-function: $(t)")
        else push!(ts_computed_2, ass_reduc(t, tterm_subst[1]))
        end
    end
    # ^ Each of these still has ITS OWN TLoc's

    prod_w_unified_args = infer_type_(EProd([]), ts_computed_2) 
    # ^ REUSING the TProd inference, HACKING the fact that Term is NOT used
    full_arity = prod_w_unified_args |> arity
    # ^Can i compute this in some smarter way?  # Dunno !
    ts_computed_res, args = Array{Type_}(prod_w_unified_args.res_type.data), TProd(prod_w_unified_args.arg_types) # Switcharoo, TProd becomes array and array becomes TProd.. What a mess

    # Then, actually unify all in/outs:

    unified_types = Array{Type_}([ts_computed_res[1]])
    prev_out = unified_types[end] # TODO fix when app is not a mess anymore
    for op in ts_computed_res[2:end]
        next_in = op.t_in # YES this always exists now
        substs =  robinsonUnify(prev_out, next_in, full_arity, full_arity)
        if substs isa Error 
            return Error("Mismatched app: get out type $(prev_out |> pr) but required type $(next_in .|> pr), with error '$(substs)'")
        end
        (s1, s2) = substs
        unified_types = Array{Type_}(unified_types .|> (x->ass_reduc(x, s1))) 
        # if they BECAME EQUAL to last_one, this should work
        # ^ Also Maybe you can SKIP updating all of them but who cares
        args = ass_reduc(args, s1) # Keep track of the Arg types, too
        push!(unified_types, ass_reduc(op, s2))
        prev_out = unified_types[end]
        # ^ POSSIBLY BROKEN: Shouldnt i look at the max arity of the ENTIRE unified_types ?
        full_arity = Inf_res(args.data, TProd(unified_types)) |> arity
        # TODO: ^ IMPROVE, i'm CERTAIN there's a better way (smthg like TProd(s1) |> arity or smthg ?)
    end
    return Inf_res(args.data, unified_types[end].t_out)
    # Returns the OUTPUT type instead of the composed TTerm type cuz this is a mess
end


tf = EAnno(EAbs(EGlob("b", TGlob("B"))), TTermAuto(TGlob("A"),  TGlob("B")))
targ = EAnno(ELoc(1), TGlob("A"))
e = EAppAuto(tf, targ)
infer_type_rec(e)

e = EAbs(EApp([EProd([ELoc(1), ELoc(1)]), ELoc(2)]))
e |> pr
infer_type_rec(e).res_type |> pr


# SHOULD be: 
TTerm(TProd([TLoc(1), TTerm(TProd([TLoc(1), TLoc(1)]), TLoc(2))]), TLoc(2)) |> pr