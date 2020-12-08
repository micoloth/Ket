
TOPFREE=100
newvar() = global TOPFREE = TOPFREE + 1

abstract type Term end
Id = String
Index = Int

struct FreeVar <: Term n::Id end
struct LocalVar <: Term n::Index end
struct BaseVal <: Term n::Index end
# struct MetaVar <: Term n::Id end
struct Uni <: Term n::Type{Term} end
struct Ap <: Term
    func::Term # must compute to a lambda
    arg::Term # must compute to a PROD
end
struct Lam <: Term body::Term end
struct Pi <: Term
    from::Term
    to::Term
end
struct Prod <: Term
    data::Array{Term}
end
struct Proj <: Term
    tag::Term
end
struct Sum <: Term
    data::Term
    tag::Index
end
struct Match <: Term
    funcs::Array{Term} # it breaks here: ASSUMPTION: each one computes a Lambda!!!!!!!!!
end

########################################## Print

pr(x::FreeVar)::String = "F$(x.n)"
pr(x::BaseVal)::String = "$(x.n)"
pr(x::LocalVar)::String = "_$(x.n)"
# pr(x::MetaVar)::String = "M$(x.n)"
pr(x::Uni)::String = "T" 
pr(x::Ap)::String = "(" * pr(x.arg) * "." * pr(x.func) *")" # join(x.func .|> pr, ".")
pr(x::Lam)::String = "/{$(pr(x.body))}" 
pr(x::Pi)::String = "($(pr(x.from))->$(pr(x.to)))" 
pr(x::Prod)::String = "[$(join(x.data .|> pr, ", ")),]" 
pr(x::Proj)::String = "[$(pr(x.tag))]"
pr(x::Sum)::String = "$(x.tag);$(pr(x.data))" 
pr(x::Match)::String = x.funcs .|> pr |> enumerate .|> (((i, s),)->"$(i)>$(s)") |> (x->join(x, ", ")) |> (x->"/{$(x)}" )

pr(Ap(Lam(LocalVar(1)), FreeVar("2")))
pr(Prod([LocalVar(3), Lam(FreeVar("a"))]))
pr(Match([Lam(LocalVar(3)), Lam(FreeVar("a"))]))


########################################## raise

raise_(base::Int, i::Int, t::FreeVar)::FreeVar = t 
raise_(base::Int, i::Int, t::BaseVal)::BaseVal = t 
# raise_(base::Int, i::Int, t::MetaVar)::MetaVar = t 
raise_(base::Int, i::Int, t::Uni)::Uni = t 
raise_(base::Int, i::Int, t::LocalVar)::LocalVar = if i>1 LocalVar(i + t.n) else t end 
raise_(base::Int, i::Int, t::Ap)::Ap = Ap(raise_(base, i, t.func), raise_(base, i, t.arg)) 
raise_(base::Int, i::Int, t::Lam)::Lam = Lam(raise_(base+1, i, t.body)) 
raise_(base::Int, i::Int, t::Pi)::Pi = Pi(raise_(base, i, t.from), raise_(base+1, i, t.to)) 

raise_(base::Int, i::Int, t::Prod)::Prod = Prod(t.data .|> (x->raise_(base, i, x))) 
raise_(base::Int, i::Int, t::Proj)::Proj = Proj(raise_(base, i, t.tag)) 
raise_(base::Int, i::Int, t::Sum)::Sum = Sum(raise_(base, i, t.data), t.tag) 
raise_(base::Int, i::Int, t::Match)::Match = Match(t.funcs .|> (x->raise_(base, i, x))) 
raise(i::Int, t::Term)::Term = raise_(1, i, t) 

Lam(Ap(LocalVar(0), LocalVar(1))) |> pr
Lam(Ap(LocalVar(0), LocalVar(1))) |> t->raise(1, t) |> pr


########################################## subst 

subst(new::Term, i::Index, t::FreeVar)::Term= t 
subst(new::Term, i::Index, t::BaseVal)::Term= t 
# subst(new::Term, i::Index, t::MetaVar)::Term k= t 
subst(new::Term, i::Index, t::Uni)::Term = t 
subst(new::Term, i::Index, t::Ap)::Term = Ap(subst(new, i, t.func), subst(new, i, t.arg)) 
subst(new::Term, i::Index, t::Lam)::Term = Lam(subst(raise(1, new), (i+1), t.body)) 
subst(new::Term, i::Index, t::Pi)::Term = Pi(subst(new, i, t.from), subst(raise(1, new), (i+1), t.to)) 
subst(new::Term, i::Index, t::Prod)::Term = Prod(t.data .|> (x->subst(new, i, x))) 
subst(new::Term, i::Index, t::Proj)::Term = Proj(subst(new, i, t.tag)) 
subst(new::Term, i::Index, t::Sum)::Term = Sum(subst(new, i, t.data), t.tag) 
subst(new::Term, i::Index, t::Match)::Term = Match(t.funcs .|> (x->subst(new, i, x))) 
function subst(new::Term, i::Index, t::LocalVar)::Term
    if t.n < i t
    elseif t.n == i new
    else LocalVar(t.n-1)
    end
end

########################################## substFV 

subst(new::Term, i::Id, t::FreeVar)::Term = if t.n == i new else t end  
subst(new::Term, i::Id, t::BaseVal)::Term = t 
subst(new::Term, i::Id, t::LocalVar)::Term = t 
subst(new::Term, i::Id, t::Uni)::Term = t 
subst(new::Term, i::Id, t::Ap)::Term = Ap(subst(new, i, t.func), subst(new, i, t.arg)) 
subst(new::Term, i::Id, t::Lam)::Term = Lam(subst(raise(1, new), i, t.body)) 
subst(new::Term, i::Id, t::Pi)::Term = Pi(subst(new, i, t.from), subst(raise(1, new), i, t.to)) 
# subst(new::Term, i::Id, t::MetaVar)::Term = t
subst(new::Term, i::Id, t::Prod)::Term = Prod(t.data .|> (x->subst(new, i, x))) 
subst(new::Term, i::Id, t::Proj)::Term = Proj(subst(new, i, t.tag)) 
subst(new::Term, i::Id, t::Sum)::Term = Sum(subst(new, i, t.data), t.tag) 
subst(new::Term, i::Id, t::Match)::Term = Match(t.funcs .|> (x->subst(new, i, x))) 


########################################## substMV 
########################################## metavars 

########################################## reduc (simple eager interpreter)

reduc(t::FreeVar)::Term = t
reduc(t::LocalVar)::Term = t
reduc(t::BaseVal)::Term = t
reduc(t::Uni)::Term = t
# reduc(t::MetaVar)::Term = t
reduc(t::Lam)::Term = Lam(reduc(t.body))
reduc(t::Pi)::Term = Pi(reduc(t.from), reduc(t.to))
reduc(t::Prod)::Term = Prod(t.data .|> reduc)
reduc(t::Proj)::Term = Proj(reduc(t.tag))
reduc(t::Sum)::Term = Sum(t.data|> reduc, t.tag)
reduc(t::Match)::Term = Match(t.funcs .|> reduc)
function reduc(t::Ap)::Term
    f = reduc(t.func)
    a = reduc(t.arg)
    if typeof(f) === Proj && typeof(f.tag) === BaseVal && typeof(a) === Prod
        reduc(a.data[f.tag.n])
    elseif typeof(f) === Match && typeof(a) === Sum
        reduc(Ap(f.funcs[a.tag], a.data))
    elseif typeof(f) === Lam
        reduc(subst(a, 1, f.body))
    else
        Ap(f, a)
    end
end
reduc(Ap(Lam(LocalVar(1)), FreeVar("50")))

Ap(Lam(Lam(LocalVar(1))), FreeVar("50")) |> pr
Ap(Lam(Lam(LocalVar(1))), FreeVar("50")) |> reduc |> pr
Ap(Ap(Lam(Lam(LocalVar(1))), FreeVar("50")), FreeVar("100")) |> pr
Ap(Ap(Lam(Lam(LocalVar(1))), FreeVar("50")), FreeVar("100")) |> reduc |> pr

reduc(Ap(Proj(BaseVal(2)), Prod([LocalVar(2), FreeVar("5")])))

# encode Map
v = Prod([Sum(FreeVar("a"), 1), Sum(FreeVar("b"), 2), Sum(FreeVar("c"), 1), Sum(FreeVar("d"), 2)])
vv = Lam(Ap(Proj(LocalVar(1)), v))
reduc(Ap(vv, BaseVal(2))) |> pr

f = Match([Lam(FreeVar("Z")), Lam(LocalVar(1))])


hh = Lam(Lam(Lam(Ap(LocalVar(3), Ap(LocalVar(2), LocalVar(1))))))  # takes [a function f and a function "v"], in two args. Returns a func with the same input as v
pr(hh)
Ap(hh, f) |> reduc |> pr
Ap(Ap(hh, f),vv) |> reduc |> pr

[1, 2,3, 4] .|> (x->reduc(Ap(Ap(Ap(hh, f), vv), BaseVal(x))) ) #.|> pr


ff = Lam(Lam(Ap(LocalVar(0), LocalVar(1))))
reduc(Ap(ff, FreeVar(3))) # the lower LocVar is the INNER one ( 0 is the INNEST)


