
# higher order typechecker using unification, copied from :

# from https://github.com/jozefg/higher-order-unification/


TOPFREE=100
newvar() = global TOPFREE = TOPFREE + 1

abstract type Term end
Id = Int
Index = Int

struct FreeVar <: Term n::Id end
struct LocalVar <: Term n::Index end
struct MetaVar <: Term n::Id end
struct Uni <: Term n::Type{Term} end
struct Ap <: Term
    l::Term
    r::Term
end
struct Lam <: Term body::Term end
struct Pi <: Term
    from::Term
    to::Term
end

########################################## Print

pr(x::FreeVar)::String = "F$(x.n)"
pr(x::LocalVar)::String = "_$(x.n)"
pr(x::MetaVar)::String = "M$(x.n)"
pr(x::Uni)::String = "T" 
pr(x::Ap)::String = "("*pr(x.l)*" "*pr(x.r)*")" 
pr(x::Lam)::String = "/{"*pr(x.body)*"}" 
pr(x::Pi)::String = "("*pr(x.from)*"->"*pr(x.to)*")" 

pr(Ap(Lam(LocalVar(1)), FreeVar(2)))


########################################## raise

raise_(base::Int, i::Int, t::FreeVar)::FreeVar = t 
raise_(base::Int, i::Int, t::MetaVar)::MetaVar = t 
raise_(base::Int, i::Int, t::Uni)::Uni = t 
raise_(base::Int, i::Int, t::LocalVar)::LocalVar = if i>0 LocalVar(i + t.n) else t end 
raise_(base::Int, i::Int, t::Ap)::Ap = Ap(raise_(base, i, t.l), raise_(base, i, t.r)) 
raise_(base::Int, i::Int, t::Lam)::Lam = Lam(raise_(base+1, i, t.body)) 
raise_(base::Int, i::Int, t::Pi)::Pi = Pi(raise_(base, i, t.from), raise_(base+1, i, t.to)) 

raise(i::Int, t::Term)::Term = raise_(0, i, t) 

Lam(Ap(LocalVar(0), LocalVar(1))) |> pr
Lam(Ap(LocalVar(0), LocalVar(1))) |> t->raise(1, t) |> pr


########################################## subst 

subst(new::Term, i::Int, t::FreeVar)::Term= t 
subst(new::Term, i::Int, t::MetaVar)::Term = t 
subst(new::Term, i::Int, t::Uni)::Term = t 
subst(new::Term, i::Int, t::Ap)::Term = Ap(subst(new, i, t.l), subst(new, i, t.r)) 
subst(new::Term, i::Int, t::Lam)::Term = Lam(subst(raise(1, new), (i+1), t.body)) 
subst(new::Term, i::Int, t::Pi)::Term = Pi(subst(new, i, t.from), subst(raise(1, new), (i+1), t.to)) 
function subst(new::Term, i::Int, t::LocalVar)::Term
    if t.n < i t
    elseif t.n == i new
    else LocalVar(t.n-1)
    end
end

########################################## substMV 

substMV(new::Term, i::Id, t::FreeVar)::Term = t 
substMV(new::Term, i::Id, t::LocalVar)::Term = t 
substMV(new::Term, i::Id, t::Uni)::Term = t 
substMV(new::Term, i::Id, t::MetaVar)::Term = if t.n == i new else t end 
substMV(new::Term, i::Id, t::Ap)::Term = Ap(substMV(new, i, t.l), substMV(new, i, t.r)) 
substMV(new::Term, i::Id, t::Lam)::Term = Lam(substMV(raise(1, new), i, t.body)) 
substMV(new::Term, i::Id, t::Pi)::Term = Pi(substMV(new, i, t.from), substMV(raise(1, new), i, t.to)) 


########################################## substFV 

substFV(new::Term, i::Id, t::FreeVar)::Term = if t.n == i new else t end  
substFV(new::Term, i::Id, t::LocalVar)::Term = t 
substFV(new::Term, i::Id, t::Uni)::Term = t 
substFV(new::Term, i::Id, t::MetaVar)::Term = t
substFV(new::Term, i::Id, t::Ap)::Term = Ap(substFV(new, i, t.l), substFV(new, i, t.r)) 
substFV(new::Term, i::Id, t::Lam)::Term = Lam(substFV(raise(1, new), i, t.body)) 
substFV(new::Term, i::Id, t::Pi)::Term = Pi(substFV(new, i, t.from), substFV(raise(1, new), i, t.to)) 


########################################## metavars 

metavars(t::FreeVar)::Set{MetaVar} = Set{MetaVar}()
metavars(t::LocalVar)::Set{MetaVar} = Set{MetaVar}()
metavars(t::Uni)::Set{MetaVar} = Set{MetaVar}()
metavars(t::MetaVar)::Set{MetaVar} = Set{MetaVar}([t])
metavars(t::Ap)::Set{MetaVar} = union(metavars(t.l), metavars(t.r))
metavars(t::Lam)::Set{MetaVar} = metavars(t.body)
metavars(t::Pi)::Set{MetaVar} = union(metavars(t.from), metavars(t.to))


########################################## isclosed 

isclosed(t::FreeVar)::Bool = false
isclosed(t::LocalVar)::Bool = true
isclosed(t::Uni)::Bool = true
isclosed(t::MetaVar)::Bool = true
isclosed(t::Ap)::Bool = isclosed(t.l) && isclosed(t.r)
isclosed(t::Lam)::Bool = isclosed(t.body)
isclosed(t::Pi)::Bool = isclosed(t.from) && isclosed(t.to)


########################################## reduc (simple eager interpreter)

reduc(t::FreeVar)::Term = t
reduc(t::LocalVar)::Term = t
reduc(t::Uni)::Term = t
reduc(t::MetaVar)::Term = t
reduc(t::Lam)::Term = Lam(reduc(t.body))
reduc(t::Pi)::Term = Pi(reduc(t.from), reduc(t.to))
function reduc(t::Ap)::Term
    f = reduc(t.l)
    if typeof(f) === Lam
        reduc(subst(t.r, 0, f.body))
    else
        Ap(f, reduc(t.r))
    end
end

reduc(Ap(Lam(LocalVar(0)), MetaVar(50)))

ff = Lam(Lam(Ap(LocalVar(0), LocalVar(1))))
reduc(Ap(ff, FreeVar(3))) # the lower LocVar is the INNER one ( 0 is the INNEST)


########################################## isStuck 

isStuck(t::MetaVar)::Bool = true
isStuck(t::Ap)::Bool = isStuck(t.l)
isStuck(t)::Bool = false


########################################## peelApTelescope (=== currying)

# (t.l, (t.r,))
peelApTelescope(t::Ap):: Tuple{Term, Array{Term}} = (pa = peelApTelescope(t.l); ( pa[1], push!(pa[2], t.r)))
peelApTelescope(t::Term)::Tuple{Term, Array{Term}} = (t, [])
peelApTelescope(Ap(Ap(Ap(Ap(FreeVar(50), FreeVar(1)), FreeVar(2)), FreeVar(3)), FreeVar(4)))


applyApTelescope(tm::Term,  args::Array)::Term = (for t in args tm = Ap(tm, t) end; tm)
applyApTelescope(FreeVar(50), [FreeVar(1), FreeVar(2), FreeVar(3), FreeVar(4)]) |> pr

saturateMV(tm::Term,  bvars::Int)::Term = applyApTelescope(tm, (0:(bvars-1)) .|> LocalVar)
saturateMV(FreeVar(50), 5) |> pr

mkLam(tm::Term, bvars::Int)::Term = (for i in 1:bvars tm = Lam(tm) end; tm)
mkLam(LocalVar(0), 5) |> pr




########################################## SIMPLIFY

# (Each of these means: Simplify the constraint "t1 must be == t2")

# question is: RECURSIVE(call simplify_) OR MANAGED (return constrains)?
    # you HAVE TO CHOSE BECAUSE YOU DON'T HAVE A MONAD.......            (i think)

# simplify :: Constraint -> UnifyM (S.Set Constraint)
# type UnifyM = LogicT (Gen Id)

struct Constraint
    t1::Term
    t2::Term
end
Error=String
SimpRes = Union{Array{Constraint}, Error}

pr(c::Constraint)::String = pr(c.t1) *"=="*pr(c.t2)

function simplify_(t1::Ap, t2::Ap)::SimpRes
    (F1, args1) = peelApTelescope(t1)
    (F2, args2) = peelApTelescope(t2)
    if F1 != F2 || length(args1) != length(args2)
        Error("Different: $(pr(F1)) != $(pr(F2)) OR $(length(args1)) != $(length(args2))")
    else
        # union([simplify_(s1, s2) for (s1, s2) in zip(args1, args2)]...)
        # union((zip(args1, args2) .|> ((a1, a2),)->simplify_(a1, a2))...)
        Array{Constraint}([Constraint(s1, s2) for (s1, s2) in zip(args1, args2)])  
    end
end

function simplify_(t1::Lam, t2::Lam)::SimpRes
    v=FreeVar(newvar())
    Array{Constraint}([Constraint(subst(v, 0, t1.body), subst(v, 0, t2.body))])
end

function simplify_(t1::Pi, t2::Pi)::SimpRes
    v=FreeVar(newvar())
    Array{Constraint}([
        Constraint(subst(v, 0, t1.to), subst(v, 0, t2.to)),
        Constraint(t1.from, t2.from)])
end

function simplify_(t1::Term, t2::Term)::SimpRes # base case
    if t1 == t2 Array{Constraint}([])
    elseif isStuck(t1) || isStuck(t2) Array{Constraint}([Constraint(t1, t2)]) 
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

function simplify(t1::Term, t2::Term)::SimpRes  # simply the toplevel interface
    t1=reduc(t1)
    t2 = reduc(t2)
    return backtrack([Constraint(t1, t2)])
    # array=[Constraint(t1, t2)]
end

simplify(c::Constraint)::SimpRes = simplify(c.t1, c.t2)


# FreeVar 0 `Ap` E === FreeVar 0 `Ap` E' 
# TO  E === E'
t1 = Ap(FreeVar(0), MetaVar(50))
t2 = Ap(FreeVar(0), MetaVar(51))
simplify(t1, t2)


t1 = Ap(Lam(LocalVar(0)), MetaVar(50))
t2 = MetaVar(51)
simplify(t1, t2)

t1 = Lam(LocalVar(0))
t2 = Lam(LocalVar(0))
simplify(t1, t2)

t = Ap(Lam(LocalVar(0)), FreeVar(1))
t1 = Ap(MetaVar(50), t)
t2 = Ap(MetaVar(51), t)
simplify(t1, t2)


t1 = Ap(FreeVar(2), MetaVar(3))
t2 = Ap(FreeVar(2), Lam(Ap(LocalVar(0), FreeVar(3))))
simplify(t1, t2)

t1 = Ap(FreeVar(2), FreeVar(3))
t2 = Ap(FreeVar(2), Lam(Ap(LocalVar(0), FreeVar(3))))
simplify(t1, t2)



################################################## All the unification stuff

Subst = Dict{Id, Term}

manySubst(s::Subst, t::Term)::Term = (for (var, val) in s  t = substMV(val, var, t) end; t )

function mergeSubst(s::Subst, t::Subst)::Union{Subst, Nothing} 
    if intersect(keys(s), keys(t)) |> isempty
        t = Subst(ii => manySubst(s, tt) for (ii, tt) in t)
        return Subst(union(t, s))
    else
        return Nothing
    end
end
mergeSubst(Subst(1=> FreeVar(5)), Subst(2=> Lam(Lam(LocalVar(1)))))


struct UnifRes_Attempts
    sub::Array{Subst}
    cs::Array{Constraint}
end
struct UnifRes_Result
    sub::Subst
    cs::Array{Constraint}
end
UnifRes = Union{UnifRes_Attempts, UnifRes_Result}


#M = λ x1. ... λ xn. xi (M1 x1 ... xn) ... (Mr x1 ... xn)  
# for ALL the xi ...
# M = λ x1. ... λ xn. A (M1 x1 ... xn) ... (Mr x1 ... xn) (if A is closed)
function generateSubst(bvars::Int, mv::Id, fnew::Term, nargs::Int)::Array{Subst}
    println("bvars", bvars)
    args = [newvar() for i in 1:nargs] .|> MetaVar .|> (tm->saturateMV(tm, bvars)) # .|> pr
    chances = (0:(bvars-1)) .|> LocalVar |> (l-> isclosed(fnew) ? vcat(l, fnew) : l) .|> (l->applyApTelescope(l, args))  .|> (l-> mkLam(l, bvars)) #  .|> pr
    # [0.. bvars) .| LocalVar . {isclosed(fnew) ? cat(x, fnew)} .| applyApTelescope<args> .| mkLam<bvars>
    # where args = [1..nargs] .| {newvar()} .| MetaVar .| saturateMV<bvars> 
    return [Subst(mv => c) for c in chances]
end

proj(bvars::Int, mv::MetaVar, fnew::Term, nnargs::Int)::Array{Subst} = [generateSubst(bvars, mv.n, fnew, nargs) for nargs in 0:nnargs] |> (x->vcat(x...))

bvars = 1
nargs =2
generateSubst(bvars, 50, MetaVar(999), nargs)
bvars = 0
nargs = 0
generateSubst(bvars, 50, MetaVar(999), nargs)

su = generateSubst(0, 50, MetaVar(999), 0)[1]
t=Ap(FreeVar(55), MetaVar(50))
manySubst(su, t)


MAX_NARGS = 3
function tryFlexRigid(t1::Ap, t2::Ap)::Array{Subst} # helper function foer unify
    (F1, args1) = peelApTelescope(t1)
    (F2, args2) = peelApTelescope(t2)
    if typeof(F1) == MetaVar && !(F1 in metavars(t2)) # && isStuck(F2) ??????
        proj(length(args1), F1, F2, MAX_NARGS)
    elseif typeof(F2) == MetaVar && !(F2 in metavars(t1)) # && isStuck(F1) ??????
        proj(length(args2), F2, F1, MAX_NARGS)
    else
        Array{Subst}([])
    end
end
tryFlexRigid(t1::Term, t2::Term)::Array{Subst} = Array{Subst}([])
tryFlexRigid(c::Constraint)::Array{Subst} = tryFlexRigid(c.t1, c.t2)

tryFlexRigid(Constraint(Ap(FreeVar(1), FreeVar(2)), Ap(MetaVar(5), FreeVar(1))))
tryFlexRigid(Constraint(Ap(MetaVar(6), FreeVar(2)), Ap(MetaVar(5), FreeVar(1))))


function unify(snew::Subst, cs::Array{Constraint}):: UnifRes # OH boi you're ALMOST needing backtrack......
    # 1. Apply the given substitution to all our constraints.
    cs1::Array{SimpRes}= cs .|> (c->Constraint(manySubst(snew, c.t1), manySubst(snew, c.t2))) .|> simplify
    #               cs1= cs .|> (c->Constraint(manySubst(snew, c.t1), manySubst(snew, c.t2))) .|> simplify
    # 2. Simplify the set of constraints to remove any obvious ones.
    if (cs1 .|> (c->typeof(c) === Error) |> any) return UnifRes_Attempts(Array{Subst}([]), Array{Constraint}([])) end 
    cs2 = cs1 |> (x->vcat(x...)) |> unique
    # 3. Separate flex-flex equations from flex-rigid ones.
    isflexflex::Array{Bool} = cs2 .|> (c->isStuck(c.t1) && isStuck(c.t2))
    #            isflexflex = cs2 .|> (c->isStuck(c.t1) && isStuck(c.t2))
    flexflexs = cs2[isflexflex]
    flexrigids = cs2[.!isflexflex]
    # 4. Pick a flex-rigid equation at random, if there are none, we're done.
    if length(flexrigids) == 0
        return UnifRes_Result(snew, flexflexs) # UHH type?
    end
    f=flexrigids[1]
    # 5. Use tryFlexRigid to get a list of possible solutions (PossibleSUBSTitutionS)
    psubsts = tryFlexRigid(f)
    # 6. RETURN each solution SO THAT YOU CAN attempt to unify the remaining constraints, backtracking if you get stuck
    psubsts::Array{Subst} = psubsts .|> s->mergeSubst(s, snew) |> (s->filter((x->typeof(x) === Subst), s))  # this is kinda the trySubsts part
    #             psubsts = psubsts .|> s->mergeSubst(s, snew) |> (s->filter(x->typeof(x) === Subst, s))  # this is kinda the trySubsts part
    return UnifRes_Attempts(psubsts, vcat(flexrigids, flexflexs))
end

# smoke test, since the semantics are so complicated:
snew =Subst(5=>FreeVar(999))
cs=[Constraint(Ap(FreeVar(999), Lam(Ap(FreeVar(90), LocalVar(0)))), Ap(MetaVar(5), MetaVar(6)))]
unify(snew,cs )


function dfs(node::Subst, cs::Array{Constraint})::Union{UnifRes_Result, Error} 
    stack::Array{UnifRes_Attempts} = [UnifRes_Attempts([node], cs)]
    #                        stack = [UnifRes_Attempts([node], cs)]
    while stack |> length > 0
        if stack[end].sub |> length > 0
            res = unify(pop!(stack[end].sub), stack[end].cs)
            if typeof(res) === UnifRes_Result return res
            else push!(stack, res) end
        else
            pop!(stack)
        end
    end
    return Error("No unifications found")
end

driver(c::Constraint)::Union{UnifRes_Result, Error} = dfs(Subst(), [c])
cs = [Constraint(Ap(FreeVar(999), Lam(Ap(FreeVar(90), LocalVar(0)))), Ap(MetaVar(5), MetaVar(6)))]
node=Subst()
driver(cs[1])

####################### lambdas and shiet

struct TypeRes_
    type::Term
    cs::Array{Constraint}
end
TypeRes = Union{Error, TypeRes_}

typeOf(ctx::Dict{Id, Term}, mctx::Dict{Id, Term}, t::LocalVar)::TypeRes = Error("wait you can't type Local Vars??? ($(t.n))")
typeOf(ctx::Dict{Id, Term}, mctx::Dict{Id, Term}, t::Uni)::TypeRes = TypeRes_(Uni(Term), [])
typeOf(ctx::Dict{Id, Term}, mctx::Dict{Id, Term}, t::FreeVar)::TypeRes= (r = get(ctx, t.n, Nothing); r!==Nothing ? TypeRes_(r, []) : Error("Undefined var: $(pr(t))"))
typeOf(ctx::Dict{Id, Term}, mctx::Dict{Id, Term}, t::MetaVar)::TypeRes = (r = get(mctx, t.n, Nothing); r!==Nothing ? TypeRes_(r, []) : Error("Undefined var: $(pr(t))"))
function typeOf(ctx::Dict{Id, Term}, mctx::Dict{Id, Term}, t::Ap)::TypeRes
    tpl, tpr = typeOf(ctx, mctx, t.l), typeOf(ctx, mctx, t.r)
    if typeof(tpl) === Error return tpl end
    if typeof(tpr) === Error return tpr end
    if typeof(tpl.type) === Pi
        TypeRes_(subst(t.r, 0, tpl.type.to), vcat(tpl.cs, tpr.cs, [Constraint(tpl.type.from, tpr.type)]))
    else
        m1, m2 = MetaVar(newvar()), MetaVar(newvar())
        TypeRes_(Ap(m2, t.r), vcat(tpl.cs, tpr.cs, [Constraint(tpr.type, m1), Constraint(tpl.type, Pi(m1, Ap(m2, LocalVar(0))))]))
    end
end

function typeOf(ctx::Dict{Id, Term}, mctx::Dict{Id, Term}, t::Lam)::TypeRes 
    v, m = newvar(), newvar()
    ctx[v] = MetaVar(m)
    mctx[m] = Uni(Term)
    typeres = typeOf(ctx, mctx, subst(FreeVar(v), 0, t.body))
    pop!(ctx, v)
    pop!(mctx, m)
    if typeof(typeres) === Error return typeres end
    return TypeRes_(Pi(MetaVar(m), substFV(LocalVar(0), v, raise(1, typeres.type))), 
                    vcat(typeres.cs, [Constraint(MetaVar(m), MetaVar(m))]))
end 
     
function typeOf(ctx::Dict{Id, Term}, mctx::Dict{Id, Term}, t::Pi)::TypeRes
    v = newvar()
    tpfrom = typeOf(ctx, mctx, t.from)
    if typeof(tpfrom) === Error return tpfrom end
    ctx[v] = t.from
    tpto = typeOf(ctx, mctx, subst(Freevar(v), 0, t.to))
    pop!(ctx, v)
    if typeof(tpto) === Error return tpto end
    return TypeRes_(Unit(Term), vcat(tpfrom.cs, tpto.cs, [Constraint(Uni(Term), tpfrom.type), Constraint(Uni(Term), tpto.type)]))
end


function test_typeof(t::Term)
    println("Term: ", pr(t))
    tr=typeOf(ctx, mctx, t)
    if typeof(tr)===Error
        println(tr)
    else
        println("Type: ", tr.type |> pr)
        print("subject to: ")
        cs = tr.cs .|> simplify 
        errors = filter((c->typeof(c) === Error), cs)  
        if length(errors)>0
            println(errors) 
        else
            cs |> (x->vcat(x...)) .|> pr |> (x->join(x, " ,  ")) |> println
        end
    end
end

ctx = Dict{Id, Term}(5=>FreeVar(50))
mctx=Dict{Id, Term}()
test_typeof(FreeVar(5))
test_typeof(LocalVar(0))
test_typeof(MetaVar(1))
test_typeof(Lam(FreeVar(5)))
test_typeof(Lam(LocalVar(0)))
test_typeof(Ap(Lam(LocalVar(0)), FreeVar(5)))
test_typeof(Lam(Ap(LocalVar(0), FreeVar(5))))
test_typeof(Lam(Ap(MetaVar(10), MetaVar(20))))
test_typeof(Lam(Ap(FreeVar(5), LocalVar(0))))




function infer(t::Term, ctx::Dict{Id, Term}, mctx::Dict{Id, Term})::TypeRes
    typeres = typeOf(ctx, mctx, t)
    if typeof(typeres) === Error return typeres end
    unires = dfs(Subst(), typeres.cs)
    if typeof(unires) === Error return Error("Empty unification") end
    return TypeRes_(manySubst(unires.sub, typeres.type), unires.cs)
end

function infer(t::Term)::TypeRes
    return infer(t::Term, Dict{Id, Term}(), Dict{Id, Term}())
end




ctx = Dict(5=>FreeVar(50), 6=>Pi(FreeVar(50), FreeVar(60)))
mctx = Dict{Id, Term}()
infer(Ap(FreeVar(6), FreeVar(5)), ctx, mctx)


ctx = Dict(5=>FreeVar(50), 6=>Pi(FreeVar(50), Ap(MetaVar(60), LocalVar(0))))
mctx = Dict{Id, Term}(7 => MetaVar(70))
infer(Ap(Ap(FreeVar(6), FreeVar(5)), MetaVar(7)), ctx, mctx)
























########################
upper(i::Int)=i*10
upper(i::String)=uppercase(i)
array = Array([1,2,3,4,"a"])
vcat!(array, ["10"])

function prrr(a)
    while length(a)>0
        println(a)
        pop!(a)
    end
end

prrr(array)


append!(array, ["10"])
for i in set 
    delete!(set, i) 
    push!(set, upper(i))
end
set
minimum()

set = Set([1,2,3,4,"a"])
pop!(set)



function sum_to(n)
    s = 0 # new local
    for i = 1:n
        s = s + i # assign existing local
    end
    return s # same local
end

sum_to(10)


Array(0:-1)

(3>5) ? 2 : 5

v = Array(12:-1:0)
v
vcat(v, 12)
v

Array[0:12]

f() =  [4,5,6, "a"]
[3, f()...]


a |> length > 0

c=[true,true, false]
push!(a, 4)
a=[4,5,6]
a[.!c]
pop!(a)
a[end]




filter((x->x<5), Set([3,4,5,6,


[[1, 2], [3]] |> (x->vcat(x...))

a = [[1, 2], [3]] 
push!(a, [4])


v,m = 2, 3
v
v, m = newvar(), newvar()

a = [1,2, 3,4,5,4,3,2,1,3,4,5,6,5,4,3,4,5]
b = [1,2]
a |> unique
c = [FreeVar(6), LocalVar(5), FreeVar(6), Ap(FreeVar(6),FreeVar(5)), Ap(FreeVar(6),FreeVar(5)), FreeVar(7)] |> unique  .|> pr

vcat(a, b, [3])

t = TypeRes_(Uni(Term), [])
(t, cs) = t


