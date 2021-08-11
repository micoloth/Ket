
# higher order typechecker using unification: Like unification.jl, but using my mylambda machinery

# from https://github.com/jozefg/higher-order-unification/


TOPFREE=100
newvar() = global TOPFREE = TOPFREE + 1

include("mylambda1.jl")

isclosed(t::TGlob)::Bool = false
isclosed(t::TLoc)::Bool = true
isclosed(t::TTop)::Bool = true
isclosed(t::TApp)::Bool = t.ops_dot_ordered .|> isclosed |> all
isclosed(t::TForall)::Bool = true
isclosed(t::TTerm)::Bool = isclosed(t.t_in) && isclosed(t.t_out)


usesLocs(t::TGlob)::Array{Index} = Array{Index}([])
usesLocs(t::TLoc)::Array{Index} = Array{Index}([t.var])
usesLocs(t::TTop)::Array{Index} = Array{Index}([])
usesLocs(t::TApp)::Array{Index} = vcat((t.ops_dot_ordered .|> usesLocs)...)
usesLocs(t::TProd)::Array{Index} = vcat((t.data .|> usesLocs)...)
usesLocs(t::TForall)::Array{Index} = Array{Index}([])
usesLocs(t::TTerm)::Array{Index} = vcat(t.t_in |> usesLocs, t.t_out |> usesLocs)


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
    Array{Constraint}([
        Constraint(t1.t_out, t2.t_out),
        # looking at tout's WITHOUT their tin's, IS what it does since it substitutes a Newvar into them..
        Constraint(t1.t_in, t2.t_in)])
end

function simplify_(t1::TLoc, t2::TLoc)::SimpRes
    Array{Constraint}([Constraint(t1, t2)])
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


# EGlob 0 `TApp` E === EGlob 0 `TApp` E' 
# TO  E === E'
t1 = TAppAuto(TGlob("T0"), TLoc(50))
t2 = TAppAuto(TGlob("T0"), TLoc(51))
simplify(t1, t2) == [Constraint(TLoc(50), TLoc(51))]

t1 = TAppAuto(TGlob("T0"), TLoc(50))
t2 = TAppAuto(TGlob("T0"), TGlob("T99"))
c = simplify(t1, t2) == [Constraint(TLoc(50), TGlob("T99"))]

t1 = TAppAuto(TForall(TLoc(1)), TLoc(50))
t2 = TLoc(51)
simplify(t1, t2) == [Constraint(TLoc(50), TLoc(51))]

t1 = TForall(TLoc(1))
t2 = TForall(TLoc(1))
simplify(t1, t2) == []

t1 = TForall(TLoc(1))
t2 = TForall(TLoc(2))
simplify(t1, t2) isa Error

t1 = TForall(TLoc(1))
t2 = TLoc(50)
simplify(t1, t2) == [Constraint(TForall(TLoc(1)), TLoc(50))]

t1 = TForall(TLoc(1))
t2 = TGlob("G")
simplify(t1, t2) == Error("Different: ∀(T1) is really different from G")

t1 = TForall(TLoc(1))
t2 = TForall(TLoc(1))
simplify(t1, t2)

t = TAppAuto(TForall(TLoc(1)), TGlob("T1"))
t1 = TAppAuto(TLoc(50), t)
t2 = TAppAuto(TLoc(51), t)
simplify(t1, t2) == [Constraint(TLoc(50), TLoc(51))]

t1 = TAppAuto(TGlob("T2"), TLoc(3))
t2 = TAppAuto(TGlob("T2"), TForall(TAppAuto(TLoc(1), TGlob("T3"))))
repr(simplify(t1, t2)) == repr([Constraint(TLoc(3), TForall(TApp([TProd([TGlob("T3")]), TLoc(1)])))])
# ^ Go fuck yourself, then die 

t1 = TAppAuto(TGlob("T2"), TGlob("T3"))
t2 = TAppAuto(TGlob("T2"), TForall(TAppAuto(TLoc(1), TGlob("T3"))))
simplify(t1, t2)  == Error("Different: T3 is really different from ∀([Just (T3).(T1)])")  # Globals cannot be "solved", and that's ok

t1 = TForall(TAppAuto(TGlob("F"), TLoc(1)))   
t2 = TForall(TAppAuto(TGlob("F"), TLoc(2)))   
simplify(t1, t2) isa Error  # LAMBDAS CANNOT BE UNIFIED (below, they are preapplied, which is a whole different discussion!!!)

t1 = TApp([TProd([TGlob("X"), TGlob("Y")]), TForall(TAppAuto(TGlob("F"), TLoc(1)))])
t2 = TApp([TProd([TGlob("Y"), TGlob("X")]), TForall(TAppAuto(TGlob("F"), TLoc(2)))])
simplify(t1, t2) == Constraint[]

t1 = TApp([TProd([TGlob("X"), TGlob("Y")]), TForall(TAppAuto(TGlob("F"), TLoc(1)))])
t2 = TApp([TProd([TGlob("X"), TGlob("Y")]), TForall(TAppAuto(TGlob("F"), TLoc(2)))])
simplify(t1, t2) == Error("Different: X is really different from Y")

t1 = TApp([TProd([TLoc(3), TLoc(2)]), TForall(TAppAuto(TGlob("F"), TLoc(1)))])
t2 = TApp([TProd([TLoc(1), TLoc(4)]), TForall(TAppAuto(TGlob("F"), TLoc(2)))])
simplify(t1, t2) == [Constraint(TLoc(3), TLoc(4))]

t1 = TApp([TProd([TGlob("X"), TLoc(2)]), TForall(TAppAuto(TLoc(2), TLoc(1)))])
t2 = TApp([TProd([TLoc(1), TLoc(4)]), TForall(TAppAuto(TGlob("F"), TLoc(2)))])
simplify(t1, t2)  == [Constraint(TGlob("X"), TLoc(4)), Constraint(TLoc(2), TGlob("F"))]

t1 = TAppAuto(TLoc(4), TGlob("X"))
t2 = TAppAuto(TTermAuto(TLoc(1), TLoc(2)), TLoc(3)) 
repr(simplify(t1, t2)) == repr([Constraint(TGlob("X"), TLoc(3)), Constraint(TLoc(4), TTerm(Type_[TLoc(1)], TLoc(2)))])
# ^ Go fuck yourself, then die 

t1 = TProd([TLoc(1), TLoc(2)])
t2 = TProd([TLoc(3), TLoc(3)])
simplify(t1, t2)


backtrack([Constraint(TLoc(1), TLoc(2)), Constraint(TLoc(3), TLoc(2))])
backtrack([Constraint(TLoc(1), TLoc(2)), Constraint(TLoc(1), TLoc(2))])
backtrack([Constraint(TLoc(1), TLoc(2)), Constraint(TLoc(2), TLoc(1))])


t1 = TProd([TLoc(1), TLoc(1)])
t2 = TProd([TGlob("F"), TGlob("G")]) #OUCHHHH
simplify(t1, t2) == [Constraint(TLoc(1), TGlob("G")), Constraint(TLoc(1), TGlob("F"))]

t1 = TProd([TLoc(1), TGlob("F")])
t2 = TProd([TGlob("G"), TLoc(1)]) #otoh, this SHOULD keep working..
simplify(t1, t2) == [Constraint(TLoc(1), TGlob("G")), Constraint(TGlob("F"), TLoc(1))]

t1 = TProd([TLoc(1), TLoc(1)])
t2 = TProd([TLoc(1), TTermAuto(TGlob("A"), TLoc(1))])
repr(simplify(t1, t2)) == repr([Constraint(TLoc(1), TLoc(1)), Constraint(TLoc(1), TTerm(Type_[TGlob("A")], TLoc(1)))])


simplify(TLoc(1), TTermAuto(TGlob("A"), TLoc(1)))
simplify(TLoc(1), TAppAuto(TGlob("A"), TLoc(1)))


# idea: in NO CASE x=f(x) can be solved, (if types_ are REDUCED), because we handle RecursiveTypes Differently!!
check_not_recursive(tloc::TLoc, tt::Type_)::Bool = !(tloc.var in usesLocs(tt) )
function check_not_recursive(c::Constraint)::Bool
    if c.t1 isa TLoc && c.t2 isa TLoc return true
    elseif c.t1 isa TLoc return check_not_recursive(c.t1, c.t2)
    elseif c.t2 isa TLoc return check_not_recursive(c.t2, c.t1)
    else throw(DomainError("Wait.. Shouldnt you simplify $(c) ?"))
    end
end





# Unify: solve f(x) = g(y) in the sense of finding x AND y 

Subst = Dict{Index, Type_}  # I'm using this as a SPARSE VECTOR
struct UsedReferences
    tloc1::Array{Index}
    tloc2::Array{Index}
    tlocUsed1::Array{Index}
    tlocUsed2::Array{Index}
end
usedReferences() = UsedReferences([], [], [], [])
newval(preferred::Index, usedReferences) = (preferred in keys(usedReferences)) ? (length(usedReferences) + 1) : preferred

function unify(t1::TForall, t2::TForall)::Union{Tuple{Subst, Subst}, Error}
    cs = simplify(t1.body, t2.body)
    s1, s2, = Subst(), Subst()  # The TLoc on the VALUES of the Dicts are the SHARED ones !!!
    shared_locs = Dict{Index, UsedReferences}() # KEYS are shared ctx here (even if, by default you DON'T change tlocs!!), using this as Sparse vector
    for c in cs if c isa Error return c end end
    for c in cs
        if c.t1 isa TLoc && c.t2 isa TLoc
            t1_assigned, t2_assigned = get(s1, c.t1.var, nothing), get(s2, c.t2.var, nothing)
            if (t1_assigned === nothing) && (t2_assigned === nothing)
                new_shared = newval(c.t1.var, shared_locs)
                shared_locs[new_shared] = UsedReferences([c.t1.var], [c.t2.var], [], [])
                s1[c.t1.var] = TLoc(new_shared)
                s2[c.t2.var] = TLoc(new_shared)
            elseif (t1_assigned === nothing) && (t2_assigned !== nothing)
                s1[c.t1.var] = t2_assigned
                # K Prob not.. --  STILL, Check usedLocs(t2_assigned) I'm afraid ... ?
            elseif (t1_assigned !== nothing) && (t2_assigned === nothing)
                s2[c.t2.var] = t1_assigned
                # K Prob not.. --  STILL, Check usedLocs(t1_assigned) I'm afraid ... ?
            elseif (t1_assigned !== nothing) && (t2_assigned !== nothing)
                cs_inside = simplify(t1_assigned, t2_assigned)
                # Recursive call from here
                # ATTENTION: these are SHARED level TLocs now!!!
            end
        elseif c.t1 isa TLoc && !(c.t2 isa TLoc)
            t1_assigned = get(s1, c.t1.var, nothing)
            t2 = turn_in_shared(c.t2, s2, shared_locs)
            if (t1_assigned === nothing)
                s1[c.t1.var] = t2
                # STILL, Check usedLocs(t2_assigned) I'm afraid ...
            elseif (t1_assigned !== nothing) # "Transitive" case: constr(1, A) AND constr(1, B) ends here
                cs_inside = simplify(t1_assigned, t2)
                # Note that t1_assigned has SHARED-level TLocs, and has Precedence !!
                # do smthgmnbvc
            end
        elseif !(c.t1 isa TLoc) && c.t2 isa TLoc
            t2_assigned = get(s2, c.t2.var, nothing)
            if (t2_assigned === nothing)
                s2[c.t2.var] = t1_assigned
                # STILL, Check usedLocs(t1_assigned) I'm afraid ...
            elseif (t2_assigned !== nothing) # "Transitive" case: constr(2, A) AND constr(2, B)
                cs_inside = simplify(t2_assigned, c.t1)
                # Note that t2_assigned has SHARED-level TLocs, and has Precedence !!
                # do smthg
            end
        elseif !(c.t1 isa TLoc) && !(c.t2 isa TLoc)
            throw(DomainError("We did say this never happens right?"))
        end
    end
end


        
        
        
        



################################################## Lambdas and shiet


isCallable_(t::TTop)::Bool = false
isCallable_(t::TGlob)::Bool = false
isCallable_(t::TLoc)::Bool = true
isCallable_(t::TForall)::Bool = isCallable_(t.body)
isCallable_(t::TApp)::Bool = (throw(DomainError("How havent you reduced this")); false)
isCallable_(t::TTerm)::Bool = true
isCallable_(t::TProd)::Bool = false

struct TypeRes_
    type::Type_
    ctx::Subst # These are the types of the ELOC's (variables)
    # IMPORTANT NOTE: ALL the type_'s here SHARE the TLoc's. 
    # This is so it becomes very easy to turn them into a TForall(TTerm(ctx, type)) # <- YES it takes an array ✔
    tarity::Int # This is the NUMBER OF TLocs's used
    # I was writing Currently used, but really, there's NOT currently
end
TypeRes = Union{Error, TypeRes_}

typeOf(t::ELoc)::TypeRes = TypeRes(TLoc(1), Subst(t.n=> TLoc(1)), 1)
function typeOf(t::EGlob)::TypeRes
    @assert arity(t.type) == 0
    TypeRes(t.type, Subst(), 0)
end
function typeOf(t::EProd, ts::Array{TypeRes_})::TypeRes
    @assert t.data|>length == ts|>length
    # UNIFICATION, unfortunately .....
    TProd(ts)
end
function typeOf(t::EAnno, tt::TypeRes_)::TypeRes 
    @assert arity(t.type) == 0
    is_ok = simplify(t.type, tt)
    for c in is_ok if c isa Error return c end end
    TypeRes(t.type, Subst(), 0)
end
function typeOf(t::EApp, ts::Array{TypeRes_})::TypeRes 
    @assert t.ops_dot_ordered|>length == ts|>length
    ts = ts .|> reduc
    @assert ts .|> (x->arity(x.type) == 0) |>all
    # ts .| {(x.type.arity) == 0} .all .assert
    # Unification of all the PAIRS..
    # BUT!! What doe it happen when a term (NOT The first) in t.ops_dot_ordered is an ELOC ??? -> HERE the deal!!!
    ts[end]
end
typeOf(t::EAbs, ttbody::Type_)::TypeRes = TTerm()





################################################## All the unification stuff


# manySubst(s::Subst, t::Type_)::Type_ = reduc(TApp([TProd([get(s, i, TLoc(i)) for i in arity(s)]), TForall(t)])) # FIX FIX, don't use arity

# function mergeSubst(s::Subst, t::Subst)::Union{Subst, Nothing} 
#     if intersect(keys(s), keys(t)) |> isempty
#         # t = Subst(ii => manySubst(s, tt) for (ii, tt) in t) # i THINK we don't need this since we are at the same level,
#         return Subst(union(t, s))
#     else
#         return Nothing # BUT i also think this is a bit too dumb??? What if it's just the same constraint twice ??? Should be the meet ? .....
#     end
# end
# mergeSubst(Subst(1=> TGlob("T5")), Subst(2=> TForall(TForall(TLoc(1)))))


# struct TunifRes_Attempts
#     sub::Array{Subst}
#     cs::Array{Constraint}
# end
# struct TunifRes_Result
#     sub::Subst
#     cs::Array{Constraint}
# end
# TunifRes = Union{TunifRes_Attempts, TunifRes_Result}


# # #M = λ x1. ... λ xn. xi (M1 x1 ... xn) ... (Mr x1 ... xn)  
# # # ... for ALL the xi from x1 to xn where the number n IS bvar ...  <-- Note that it's ALSO the number of params !!!
# # # PLUS, finally, (BUT ONLY if "fnew" is closed,)
# # # M = λ x1. ... λ xn. "fnew" (M1 x1 ... xn) ... (Mr x1 ... xn)
# # # ^ NOTE that there is a RANDOM number of these applied terms Mr here, and this is >nargs< (nargs is r).
# # function generateSubst(bvars::Int, mv::Id, fnew::Type_, nargs::Int, current_arity::Int)::Array{Subst}
# #     args_each = TProd([TLoc(i) for i in 1:bvars])
# #     args = [i + current_arity for i in 1:nargs] .|> TLoc .|> (m->TApp([])) # .|> pr  # EACH of these is a parenthesis  --> (Mr x1 ... xn) <--
# #     chances = (0:(bvars-1)) .|> LocalVar |> (l-> isclosed(fnew) ? vcat(l, fnew) : l) .|> (l->applyApTelescope(l, args))  .|> (l-> mkLam(l, bvars)) #  .|> pr
# #     # [0.. bvars) .| LocalVar . {isclosed(fnew) ? cat(x, fnew)} .| applyApTelescope<args> .| mkLam<bvars>
# #     # where args = [1..nargs] .| {newvar()} .| MetaVar .| saturateMV<bvars> 
# #     return [Subst(mv => c) for c in chances]
# # end
# # using Combinatorics
# # permutations
# # [p for p in permutations([1,2,3,4])] |> x->hcat(x...)

# function generateSubst(bvars::Int, mv::Id, fnew::Type_, nargs::Int, current_arity::Int)::Array{Subst}
#     chances = [TForall(TAppAuto(TLoc(1), TLoc(2))), TForall(TAppAuto(TLoc(2), TLoc(1))), TForall(TApp([TProd([TLoc(1), TLoc(2)]), fnew]))]
#     return [Subst(mv => c) for c in chances]
# end

# proj(bvars::Int, mv::TLoc, fnew::Type_, nnargs::Int, current_arity::Int)::Array{Subst} = [generateSubst(bvars, mv.var, fnew, nargs, current_arity) for nargs in 0:nnargs] |> (x->vcat(x...))

# bvars = 1
# nargs =2
# generateSubst(bvars, 50, TLoc(999), nargs)
# bvars = 0
# nargs = 0
# generateSubst(bvars, 50, TLoc(999), nargs)  # [Dict(50 => TLoc(999))]
# bvars = 0
# nargs = 1
# generateSubst(bvars, 50, TLoc(999), nargs)  # [Dict(50 => Ap(TLoc(999), TLoc(102)))]
# bvars = 0
# nargs = 2
# generateSubst(bvars, 50, TLoc(999), nargs)  # [ Dict(50 => Ap(Ap(TLoc(999), TLoc(103)), TLoc(104)))]
# bvars = 1
# nargs = 0
# generateSubst(bvars, 50, TLoc(999), nargs)  # [ Dict(50 => Lam(LocalVar(0)))
#                                                # Dict(50 => Lam(TLoc(999)))]
# bvars = 1
# nargs = 1
# generateSubst(bvars, 50, MetaVar(999), nargs)  # [  Dict(50 => Lam(Ap(LocalVar(0), Ap(MetaVar(109), LocalVar(0)))))
#                                                #    Dict(50 => Lam(Ap(MetaVar(999), Ap(MetaVar(109), LocalVar(0)))))]
#                     # Here it's where it gets SUPER real!!! (all terms are there)




# MAX_NARGS = 3
# function tryFlexRigid(t1::TApp, t2::TApp)::Array{Subst} # helper function foer unify
#     (F1, args1) = (t1.ops_dot_ordered[2], t1.ops_dot_ordered[1])
#     (F2, args2) = (t2.ops_dot_ordered[2], t2.ops_dot_ordered[1])
#     if typeof(F1) ==TLoc #&& !(F1 in metavrs(t2)) # && isStuck(F2) ??????
#         proj(length(args1.data), F1, F2, MAX_NARGS, 0)
#     elseif typeof(F2) == TLoc #&& !(F2 in metavars(t1)) # && isStuck(F1) ??????
#         proj(length(args2.data), F2, F1, MAX_NARGS, 0)
#     else
#         Array{Subst}([])
#     end
# end
# tryFlexRigid(t1::Type_, t2::Type_)::Array{Subst} = Array{Subst}([])
# tryFlexRigid(c::Constraint)::Array{Subst} = tryFlexRigid(c.t1, c.t2)

# tryFlexRigid(Constraint(TAppAuto(TGlob("T1"), TGlob("T2")), TAppAuto(TLoc(5), TGlob("T1"))))
# tryFlexRigid(Constraint(TAppAuto(TLoc(6), TGlob("T2")), TAppAuto(TLoc(5), TGlob("T1"))))


# function unify(snew::Subst, cs::Array{Constraint}):: TunifRes # OH boi you're ALMOST needing backtrack......
#     # 1. Apply the given substitution to all our constraints.
#     cs1::Array{SimpRes}= cs .|> (c->Constraint(manySubst(snew, c.t1), manySubst(snew, c.t2))) .|> simplify
#     #               cs1= cs .|> (c->Constraint(manySubst(snew, c.t1), manySubst(snew, c.t2))) .|> simplify
#     # 2. Simplify the set of constraints to remove any obvious ones.
#     if (cs1 .|> (c->typeof(c) === Error) |> any) return TunifRes_Attempts(Array{Subst}([]), Array{Constraint}([])) end 
#     cs2 = cs1 |> (x->vcat(x...)) |> unique
#     # 3. Separate flex-flex equations from flex-rigid ones.
#     isflexflex::Array{Bool} = cs2 .|> (c->isStuck(c.t1) && isStuck(c.t2))
#     #            isflexflex = cs2 .|> (c->isStuck(c.t1) && isStuck(c.t2))
#     flexflexs = cs2[isflexflex]
#     flexrigids = cs2[.!isflexflex]
#     # 4. Pick a flex-rigid equation at random, if there are none, we're done.
#     if length(flexrigids) == 0
#         return TunifRes_Result(snew, flexflexs) # UHH type?
#     end
#     f=flexrigids[1]
#     # 5. Use tryFlexRigid to get a list of possible solutions (PossibleSUBSTitutionS)
#     psubsts = tryFlexRigid(f)
#     # 6. RETURN each solution SO THAT YOU CAN attempt to unify the remaining constraints, backtracking if you get stuck
#     psubsts::Array{Subst} = psubsts .|> s->mergeSubst(s, snew) |> (s->filter((x->typeof(x) === Subst), s))  # this is kinda the trySubsts part
#     #             psubsts = psubsts .|> s->mergeSubst(s, snew) |> (s->filter(x->typeof(x) === Subst, s))  # this is kinda the trySubsts part
#     return TunifRes_Attempts(psubsts, vcat(flexrigids, flexflexs))
# end

# # smoke test, since the semantics are so complicated:
# snew =Subst(5=>EGlob(999))
# cs=[Constraint(TAppAuto(EGlob(999), TForall(TAppAuto(EGlob(90), ELoc(0)))), TAppAuto(TLoc(5), TLoc(6)))]
# unify(snew,cs )


# function dfs(node::Subst, cs::Array{Constraint})::Union{TunifRes_Result, Error} 
#     stack::Array{TunifRes_Attempts} = [TunifRes_Attempts([node], cs)]
#     #                        stack = [TunifRes_Attempts([node], cs)]
#     while stack |> length > 0
#         if stack[end].sub |> length > 0
#             res = unify(pop!(stack[end].sub), stack[end].cs)
#             if typeof(res) === TunifRes_Result return res
#             else push!(stack, res) end
#         else
#             pop!(stack)
#         end
#     end
#     return Error("No unifications found")
# end

# driver(c::Constraint)::Union{TunifRes_Result, Error} = dfs(Subst(), [c])
# cs = [Constraint(TAppAuto(EGlob(999), TForall(TAppAuto(EGlob(90), ELoc(0)))), TAppAuto(TLoc(5), TLoc(6)))]
# node=Subst()
# driver(cs[1])

####################### lambdas and shiet



