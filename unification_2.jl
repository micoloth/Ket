
# higher order typechecker using unification: Like unification.jl, but using my mylambda machinery

# from https://github.com/jozefg/higher-order-unification/


TOPFREE=100
newvar() = global TOPFREE = TOPFREE + 1

include("mylambda1.jl")

usesLocs(t::TGlob)::Array{Index} = Array{Index}([])
usesLocs(t::TLoc)::Array{Index} = Array{Index}([t.var])
usesLocs(t::TTop)::Array{Index} = Array{Index}([])
usesLocs(t::TApp)::Array{Index} = vcat((t.ops_dot_ordered .|> usesLocs)...)
usesLocs(t::TProd)::Array{Index} = vcat((t.data .|> usesLocs)...)
usesLocs(t::TForall)::Array{Index} = Array{Index}([])
usesLocs(t::TTerm)::Array{Index} = vcat(vcat((t.t_in .|> usesLocs)...), t.t_out |> usesLocs)


########################################## SIMPLIFY

# (Each of these means: Simplify the constraint "t1 must be == t2")

# question is: RECURSIVE(call simplify_) OR MANAGED (return constrains)?
    # you HAVE TO CHOSE BECAUSE YOU DON'T HAVE A MONAD.......            (i think)

# simplify :: Constraint -> TunifyM (S.Set Constraint)
# type TunifyM = LogicT (Gen Id)

struct Constraint
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
        Array{Constraint}([Constraint(s1, s2) for (s1, s2) in zip(t1.ops_dot_ordered, t2.ops_dot_ordered)])  
    end    
end

function simplify_(t1::TProd, t2::TProd)::SimpRes
    if length(t1.data) != length(t2.data)
        Error("Different lengths: $(length(t1.data)) != $(length(t2.data))")
    else
        Array{Constraint}([Constraint(s1, s2) for (s1, s2) in zip(t1.data, t2.data)])  
    end    
    # union([simplify_(s1, s2) for (s1, s2) in zip(args1, args2)]...)
    # union((zip(args1, args2) .|> ((a1, a2),)->simplify_(a1, a2))...)
    # Array{Constraint}([Constraint(s1, s2) for (s1, s2) in zip(args1.data, args2.data)])  
end

function simplify_(t1::TForall, t2::TForall)::SimpRes
    println("Simplyfing two Foralls:")
    cons = Constraint(t1.body, t2.body)
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
    vcat(
        Array{Constraint}([Constraint(t1.t_out, t2.t_out)]),
        # looking at tout's WITHOUT their tin's, IS what it does since it substitutes a Newvar into them..
        [Constraint(t, u) for (t, u) in zip(t1.t_in, t2.t_in)])
end

function simplify_(t1::TLoc, t2::TLoc)::SimpRes
    Array{Constraint}([Constraint(t1, t2)])
end

function simplify_(t1::TSum, t2::TSum)::SimpRes
    if length(t1.data) != length(t2.data)
        Error("Different lengths: $(length(t1.data)) != $(length(t2.data))")
    else
        Array{Constraint}([Constraint(s1, s2) for (s1, s2) in zip(t1.data, t2.data)])  
    end 
end

function simplify_(t1::Type_, t2::Type_)::SimpRes # base case
    if t1 == t2 Array{Constraint}([])
    elseif typeof(t1) === TLoc || typeof(t2) === TLoc Array{Constraint}([Constraint(t1, t2)]) 
    else Error("Different: $(pr(t1)) is really different from $(pr(t2))")
    end
end

simplify_(c::Constraint)::SimpRes = simplify_(c.t1, c.t2)


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
    return backtrack(Array{Constraint}([Constraint(t1, t2)]))
    # array=[Constraint(t1, t2)]
end

simplify(c::Constraint)::SimpRes = simplify(c.t1, c.t2)



# Unify: solve f(x) = g(y) in the sense of finding x AND y 

Subst = Dict{Index, Type_}  # I'm using this as a SPARSE VECTOR
# struct UsedReferences
#     tloc1::Array{Index}
#     tloc2::Array{Index}
#     tlocUsed1::Array{Index}
#     tlocUsed2::Array{Index}
# end
# usedReferences() = UsedReferences([], [], [], [])
# newval(preferred::Index, usedReferences) = (preferred in keys(usedReferences)) ? (length(usedReferences) + 1) : preferred


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
sr(t...) = get_reduc_subst(collect(t)) |> reduc


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

     
function robinsonUnify(t1::TForall, t2::TForall)::Union{Tuple{TProd, TProd}, Error}
    # Dumb, i promise i'll make this better:

    # Not gonna lie, i Did like this a lot...
    # new_shared = newval(c.t1.var, shared_locs)
    # shared_locs[new_shared] = UsedReferences([c.t1.var], [c.t2.var], [], [])
    # s1[c.t1.var] = TLoc(new_shared)

    t1arity, t2arity = t1.body |> arity, t2.body |> arity
    t1 = TApp([TProd([TLoc(i) for i in 1:t1arity]), t1])
    t2 = TApp([TProd([TLoc(i) for i in (t1arity+1):(t1arity+t2arity)]), t2])
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

    current_arity = t1arity + t2arity
    current_total_subst = TProd([]) # PLACEHOLDER
    subst_prods = Array{TProd}([]) # To pass into get_reduc_subst IN THIS ORDER:
    for (i, tt) in middle_subst
        if length(subst_prods) > 0
            tt_updated = get_reduc_subst(Array{Type_}([tt, current_total_subst])) |> reduc
            i_updated = get_reduc_subst(Array{Type_}([TLoc(i), current_total_subst])) |> reduc
        else
            i_updated, tt_updated = TLoc(i), tt
        end
        new_subst = get_subst_prod(i_updated, tt_updated, current_arity)
        push!(subst_prods, new_subst)
        current_arity = arity(subst_prods[end]) # The beauty of this is this is Enough... I HOPE LOL
        if length(subst_prods) > 1
            current_total_subst = get_reduc_subst(Array{Type_}([current_total_subst, new_subst])) |> reduc
        else
            current_total_subst = new_subst
        end
    end
    if length(subst_prods) == 0
        @assert (t1arity == t2arity) "$(t1arity) != $(t2arity), HOW tho ..."
        # TODO: remove this dumb shit, replace with LITERALLY NOTHING
        return TProd([TLoc(i) for i in 1:t1arity]), TProd([TLoc(i) for i in 1:t1arity])
    end
    
    subst1 = TProd(current_total_subst.data[1:t1arity])
    subst2 = TProd(current_total_subst.data[(t1arity+1):(t1arity+t2arity)])
    return subst1, subst2
end
    

# TProd([TLoc(1), TTerm([TLoc(2)], TLoc(3))])
# get_subst_prod(TLoc(1), TTermAuto(TLoc(2), TLoc(3)), 3)


# TESTS:

function test_unify(t1, t2)
    (s1, s2) = robinsonUnify(TForall(t1), TForall(t2))
    red1 = reduc(TApp([s1, TForall(t1)])) 
    println("reduced term: ", red1 |> pr)
    red1 == reduc(TApp([s2, TForall(t2)]))
end

t1 = TAppAuto(TGlob("G0"), TLoc(1))
t2 = TAppAuto(TGlob("G0"), TLoc(2))
simplify(t1, t2) == [Constraint(TLoc(1), TLoc(2))]
robinsonUnify(TForall(t1), TForall(t2))
test_unify(t1, t2)

t1 = TAppAuto(TGlob("G0"), TLoc(1))
t2 = TAppAuto(TGlob("G0"), TGlob("G99"))
c = simplify(t1, t2) == [Constraint(TLoc(1), TGlob("G99"))]
robinsonUnify(TForall(t1), TForall(t2))
test_unify(t1, t2)

t1 = TAppAuto(TForall(TLoc(1)), TLoc(1))
t2 = TLoc(2)
simplify(t1, t2) == [Constraint(TLoc(1), TLoc(2))]
robinsonUnify(TForall(t1), TForall(t2))
test_unify(t1, t2)

t1 = TForall(TLoc(1))
t2 = TForall(TLoc(1))
simplify(t1, t2) == []
robinsonUnify(TForall(t1), TForall(t2))
test_unify(t1, t2)

t1 = TForall(TLoc(1))
t2 = TForall(TLoc(2))
simplify(t1, t2) isa Error
robinsonUnify(TForall(t1), TForall(t2))

t1 = TForall(TLoc(1))
t2 = TLoc(3)
simplify(t1, t2) == [Constraint(TForall(TLoc(1)), TLoc(3))]
robinsonUnify(TForall(t1), TForall(t2))
test_unify(t1, t2)

t1 = TForall(TLoc(1))
t2 = TGlob("G")
simplify(t1, t2) == Error("Different: ∀(T1) is really different from G")
robinsonUnify(TForall(t1), TForall(t2))

t1 = TForall(TLoc(1))
t2 = TForall(TLoc(1))
simplify(t1, t2)
robinsonUnify(TForall(t1), TForall(t2))
test_unify(t1, t2)

t = TAppAuto(TForall(TLoc(1)), TGlob("G1"))
t1 = TAppAuto(TLoc(3), t)
t2 = TAppAuto(TLoc(4), t)
simplify(t1, t2) == [Constraint(TLoc(3), TLoc(4))]
robinsonUnify(TForall(t1), TForall(t2))
test_unify(t1, t2)

t1 = TAppAuto(TGlob("G2"), TLoc(3))
t2 = TAppAuto(TGlob("G2"), TForall(TAppAuto(TLoc(1), TGlob("G3"))))
repr(simplify(t1, t2)) == repr([Constraint(TLoc(3), TForall(TApp([TProd([TGlob("G3")]), TLoc(1)])))])
# ^ Go fuck yourself, then die 
robinsonUnify(TForall(t1), TForall(t2))
test_unify(t1, t2)

t1 = TAppAuto(TGlob("G2"), TGlob("G3"))
t2 = TAppAuto(TGlob("G2"), TForall(TAppAuto(TLoc(1), TGlob("G3"))))
simplify(t1, t2)  == Error("Different: T3 is really different from ∀([Just (T3).(T1)])")  # Globals cannot be "solved", and that's ok
robinsonUnify(TForall(t1), TForall(t2))

t1 = TForall(TAppAuto(TGlob("F"), TLoc(1)))   
t2 = TForall(TAppAuto(TGlob("F"), TLoc(2)))   
simplify(t1, t2) isa Error  # LAMBDAS CANNOT BE UNIFIED (below, they are preapplied, which is a whole different discussion!!!)
robinsonUnify(TForall(t1), TForall(t2))

t1 = TApp([TProd([TGlob("X"), TGlob("Y")]), TForall(TAppAuto(TGlob("F"), TLoc(1)))])
t2 = TApp([TProd([TGlob("Y"), TGlob("X")]), TForall(TAppAuto(TGlob("F"), TLoc(2)))])
simplify(t1, t2) == Constraint[]
robinsonUnify(TForall(t1), TForall(t2))
test_unify(t1, t2)

t1 = TApp([TProd([TGlob("X"), TGlob("Y")]), TForall(TAppAuto(TGlob("F"), TLoc(1)))])
t2 = TApp([TProd([TGlob("X"), TGlob("Y")]), TForall(TAppAuto(TGlob("F"), TLoc(2)))])
simplify(t1, t2) == Error("Different: X is really different from Y")
robinsonUnify(TForall(t1), TForall(t2))

t1 = TApp([TProd([TLoc(3), TLoc(2)]), TForall(TAppAuto(TGlob("F"), TLoc(1)))])
t2 = TApp([TProd([TLoc(1), TLoc(4)]), TForall(TAppAuto(TGlob("F"), TLoc(2)))])
simplify(t1, t2) == [Constraint(TLoc(3), TLoc(4))]
robinsonUnify(TForall(t1), TForall(t2))
test_unify(t1, t2)

t1 = TApp([TProd([TGlob("X"), TLoc(2)]), TForall(TAppAuto(TLoc(2), TLoc(1)))])
t2 = TApp([TProd([TLoc(1), TLoc(4)]), TForall(TAppAuto(TGlob("F"), TLoc(2)))])
simplify(t1, t2)  == [Constraint(TGlob("X"), TLoc(4)), Constraint(TLoc(2), TGlob("F"))]
robinsonUnify(TForall(t1), TForall(t2))
test_unify(t1, t2)

t1 = TAppAuto(TLoc(4), TGlob("X"))
t2 = TAppAuto(TTermAuto(TLoc(1), TLoc(2)), TLoc(3)) 
repr(simplify(t1, t2)) == repr([Constraint(TGlob("X"), TLoc(3)), Constraint(TLoc(4), TTerm(Type_[TLoc(1)], TLoc(2)))])
# ^ Go fuck yourself, then die 
robinsonUnify(TForall(t1), TForall(t2))
test_unify(t1, t2)

t1 = TProd([TLoc(1), TLoc(2)])
t2 = TProd([TLoc(3), TLoc(3)])
simplify(t1, t2)
robinsonUnify(TForall(t1), TForall(t2))
test_unify(t1, t2)

t1 = TProd([TLoc(1), TLoc(1)])
t2 = TProd([TGlob("F"), TGlob("G")]) #OUCHHHH
simplify(t1, t2) == [Constraint(TLoc(1), TGlob("G")), Constraint(TLoc(1), TGlob("F"))]
robinsonUnify(TForall(t1), TForall(t2)) # Error, nice

t1 = TProd([TLoc(1), TGlob("F")])
t2 = TProd([TGlob("G"), TLoc(1)]) #otoh, this SHOULD keep working..
simplify(t1, t2) == [Constraint(TLoc(1), TGlob("G")), Constraint(TGlob("F"), TLoc(1))]
robinsonUnify(TForall(t1), TForall(t2))
test_unify(t1, t2)

t1 = TProd([TLoc(1), TLoc(1)])
t2 = TProd([TLoc(1), TTermAuto(TGlob("A"), TLoc(1))])
repr(simplify(t1, t2)) == repr([Constraint(TLoc(1), TLoc(1)), Constraint(TLoc(1), TTerm(Type_[TGlob("A")], TLoc(1)))])
robinsonUnify(TForall(t1), TForall(t2)) # Recursive Error, nice!

t1 = TProd([TLoc(1), TLoc(1), TLoc(2), TLoc(2)])
t2 = TProd([TLoc(1), TLoc(2), TLoc(2), TTermAuto(TGlob("A"), TTermAuto(TGlob("B"), TLoc(1)))])
repr(simplify(t1, t2)) == repr([Constraint(TLoc(2), TTerm(Type_[TGlob("A")], TTerm(Type_[TGlob("B")], TLoc(1)))), Constraint(TLoc(1), TLoc(1)), Constraint(TLoc(2), TLoc(2)), Constraint(TLoc(1), TLoc(2))])
robinsonUnify(TForall(t1), TForall(t2)) # Recursive Error, nice!

t1 = TProd([TLoc(1), TLoc(1), TLoc(2), TLoc(2)])
t2 = TProd([TTermAuto(TGlob("A"), TTermAuto(TGlob("B"), TGlob("C"))), TLoc(2), TLoc(2), TTermAuto(TGlob("A"), TTermAuto(TGlob("B"), TLoc(1)))])
repr(simplify(t1, t2)) == repr(Constraint[Constraint(TLoc(2), TLoc(2)), Constraint(TLoc(1), TTerm(Type_[TGlob("A")], TTerm(Type_[TGlob("B")], TGlob("C")))), Constraint(TLoc(2), TTerm(Type_[TGlob("A")], TTerm(Type_[TGlob("B")], TLoc(1)))), Constraint(TLoc(1), TLoc(2))])
robinsonUnify(TForall(t1), TForall(t2))
test_unify(t1, t2)   #####  YESSSSS

t1 = TProd([TLoc(1), TLoc(2)])
t2 = TProd([TLoc(2), TTermAuto(TGlob("A"), TLoc(1))])
repr(simplify(t1, t2)) == "Constraint[Constraint(TLoc(2), TTerm(Type_[TGlob(\"A\")], TLoc(1))), Constraint(TLoc(1), TLoc(2))]"
robinsonUnify(TForall(t1), TForall(t2))
test_unify(t1, t2)

t1 = TProd([TLoc(1), TLoc(1), TLoc(2), TLoc(2)])
t2 = TProd([TGlob("F"), TLoc(3), TLoc(3), TGlob("G")])
simplify(t1, t2) == [Constraint(TLoc(2), TGlob("G")), Constraint(TLoc(1), TLoc(3)), Constraint(TLoc(1), TGlob("F")), Constraint(TLoc(2), TLoc(3))]
robinsonUnify(TForall(t1), TForall(t2)) # Error, nice

t1 = TProd([TLoc(1), TLoc(1), TLoc(2), TLoc(2)])
t2 = TProd([TGlob("F"), TLoc(1), TLoc(1), TGlob("G")])
simplify(t1, t2) == [Constraint(TLoc(2), TLoc(1)), Constraint(TLoc(1), TLoc(1)), Constraint(TLoc(2), TGlob("G")), Constraint(TLoc(1), TGlob("F")), ]
robinsonUnify(TForall(t1), TForall(t2)) # Error, nice

function prepTransEx(l, g1, g2)
    v1=vcat([[TLoc(i), TLoc(i)] for i in 1:l]...)
    v2=vcat([[TLoc(i), TLoc(i)] for i in 1:l-1]...)
    TProd(v1), TProd(vcat([TGlob(g1)], v2, [TGlob(g2)]))
end
t1, t2 = prepTransEx(50, "F", "F")
robinsonUnify(TForall(t1), TForall(t2))
test_unify(t1, t2)

t1, t2 = prepTransEx(10, "F", "G")
robinsonUnify(TForall(t1), TForall(t2))












# Each TLoc refers to position in the row BELOW:
t1 = TProd([TTerm([TLoc(1)], TLoc(2)), TLoc(3)])
t2 = TProd([TLoc(1), TLoc(2), TLoc(2)])
t3 = TProd([TGlob("G"), TLoc(1)])
t4 = TProd([TTerm([TGlob("A")], TGlob("B"))])
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
t1 = TProd([TLoc(1), TGlob("F"), TLoc(3), TTerm([TLoc(4)], TLoc(5))])
t2 = TProd([TLoc(1), TGlob("SKIPPED"), TTerm([TLoc(2)], TLoc(3)), TLoc(1), TLoc(1)])
t3 = TProd([TLoc(2), TLoc(1), TLoc(2)])
t4 = TProd([TLoc(1), TTerm([TLoc(2)], TLoc(3))])
t5 = TProd([TLoc(2), TGlob("Z"), TGlob("Z")])
get_reduc_subst([t1, t2, t3, t4, t5]) |> reduc |> pr == "[Z->Z x F x T2->Z->Z x Z->Z->Z->Z]"

sr(sr(t1, t2), sr(t3, t4, t5)) |> pr
sr(sr(t1, t2, t3, t4), t5) |> pr
sr(t1, sr(t2, t3), sr(t4, t5)) |> pr
