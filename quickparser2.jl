
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
struct Lam <: Term 
    body::Term 
    # nargs::Index
end
struct Prod <: Term
    data::Array{Term}
end
# struct Proj <: Term
#     tag::Term
# end
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
pr(x::Ap)::String = "(" * pr(x.arg) * " ." * pr(x.func) *")" # join(x.func .|> pr, ".")
pr(x::Lam)::String = "/{$(pr(x.body))}" 
pr(x::Prod)::String = "[$(join(x.data .|> pr, ", ")),]" 
# pr(x::Proj)::String = "[$(pr(x.tag))]"
pr(x::Sum)::String = "$(x.tag);$(pr(x.data))" 
pr(x::Match)::String = x.funcs .|> pr |> enumerate .|> (((i, s),)->"$(i)>$(s)") |> (x->join(x, ", ")) |> (x->"/{$(x)}" )


########################################## arity (hopefully types will make this useless?)
# arity(base::Index, t::FreeVar)::Index= base 
# arity(base::Index, t::BaseVal)::Index= base 
# arity(base::Index, t::LocalVar)::Index = max(base, t.n)
# # arity(base::Index, t::MetaVar)::Index k= t 
# arity(base::Index, t::Uni)::Index = t 
# arity(base::Index, t::Ap)::Index = max(arity(base, t.func), arity(base, t.arg)) 
# arity(base::Index, t::Lam)::Index = base # Lam(arity(base, t.body)) 
# arity(base::Index, t::Prod)::Index = reduce(max, t.data .|> (x->arity(base, x))) 
# # arity(base::Index, t::Proj)::Index = arity(base, t.tag)
# arity(base::Index, t::Sum)::Index = arity(base, t.data)
# arity(base::Index, t::Match)::Index = reduce(max, t.funcs .|> (x->arity(base, x))) 
# arity(t::Term)::Index = arity(0, t)

# Lam(body::Term) = Lam(body,arity(body))

Lam(Ap(LocalVar(1), LocalVar(2)))

pr(Ap(Lam(LocalVar(1)), FreeVar("2")))
pr(Prod([LocalVar(3), Lam(FreeVar("a"))]))
pr(Match([Lam(LocalVar(3)), Lam(FreeVar("a"))]))

########################################## raise

# raise_(base::Int, i::Int, t::FreeVar)::FreeVar = t 
# raise_(base::Int, i::Int, t::BaseVal)::BaseVal = t 
# # raise_(base::Int, i::Int, t::MetaVar)::MetaVar = t 
# raise_(base::Int, i::Int, t::Uni)::Uni = t 
# raise_(base::Int, i::Int, t::LocalVar)::LocalVar = if i>1 LocalVar(i + t.n) else t end 
# raise_(base::Int, i::Int, t::Ap)::Ap = Ap(raise_(base, i, t.func), raise_(base, i, t.arg)) 
# raise_(base::Int, i::Int, t::Lam)::Lam = Lam(raise_(base+1, i, t.body)) 

# raise_(base::Int, i::Int, t::Prod)::Prod = Prod(t.data .|> (x->raise_(base, i, x))) 
# # raise_(base::Int, i::Int, t::Proj)::Proj = Proj(raise_(base, i, t.tag)) 
# raise_(base::Int, i::Int, t::Sum)::Sum = Sum(raise_(base, i, t.data), t.tag) 
# raise_(base::Int, i::Int, t::Match)::Match = Match(t.funcs .|> (x->raise_(base, i, x))) 
# raise(i::Int, t::Term)::Term = raise_(1, i, t) 

# Lam(Ap(LocalVar(0), LocalVar(1))) |> pr
# Lam(Ap(LocalVar(0), LocalVar(1))) |> t->raise(1, t) |> pr


########################################## subst 

subst(news::Array{Term}, t::FreeVar)::Term= t 
subst(news::Array{Term}, t::BaseVal)::Term= t 
subst(news::Array{Term}, t::LocalVar)::Term = if t.n <= length(news) news[t.n] else throw(DomainError("Undefined local var $(t.n), n args given = $(length(news))" )) end
# subst(news::Array{Term}, t::MetaVar)::Term k= t 
subst(news::Array{Term}, t::Uni)::Term = t 
subst(news::Array{Term}, t::Ap)::Term = Ap(subst(news, t.func), subst(news, t.arg)) 
subst(news::Array{Term}, t::Lam)::Term = t # Lam(subst(news, t.body)) 
subst(news::Array{Term}, t::Prod)::Term = Prod(t.data .|> (x->subst(news, x))) 
# subst(news::Array{Term}, t::Proj)::Term = Proj(subst(news, t.tag)) 
subst(news::Array{Term}, t::Sum)::Term = Sum(subst(news, t.data), t.tag) 
subst(news::Array{Term}, t::Match)::Term = Match(t.funcs .|> (x->subst(news, x))) 
#throw(DomainError("Undefined local var $(t.n), n args = $(length(news))" ))

########################################## substFV 
########################################## substMV 
########################################## metavars 

########################################## reduc (simple eager interpreter)

reduc(t::FreeVar)::Term = t
reduc(t::LocalVar)::Term = t
reduc(t::BaseVal)::Term = t
reduc(t::Uni)::Term = t
# reduc(t::MetaVar)::Term = t
reduc(t::Lam)::Term = Lam(reduc(t.body))
reduc(t::Prod)::Term = Prod(t.data .|> reduc)
reduc(t::Sum)::Term = Sum(t.data|> reduc, t.tag)
reduc(t::Match)::Term = Match(t.funcs .|> reduc)
reduc(t::Ap)::Term = (t|>pr|>println; reduc(reduc(t.func), reduc(t.arg))) # Ap is AN OBJECT THAT REPRESENTS A COMPUTATION (it's only "reduc" here since which one is "typechecked at runtime")
function reduc(func::BaseVal, arg::Prod) # VERY IMPORTANT: I'm deciding INDEX is the FUNC here (fairly arbitrary)
    println("> doing the ", typeof(func),  " ", typeof(arg), " thing")
    temp = arg.data[func.n]
    print(" creating > ", temp|>pr, "\n")
    reduc(temp)
end
function reduc(func::Match, arg::Sum)
    println("> doing the ", typeof(func),  " ", typeof(arg), " thing")
    temp = Ap(func.funcs[arg.tag], arg.data)
    print( "creating   >  ", temp|>pr, "\n")
    reduc(temp)
end
function reduc(func::Lam, arg::Prod)
    println("> doing the ", typeof(func),  " ", typeof(arg), " thing")
    temp = subst(arg.data, func.body)
    print( "creating  > ", temp|>pr, "\n")
    reduc(temp)
end
function reduc(func, arg)
        println("> STOP, since apparently they are ", typeof(func),  " ", typeof(arg), " ...")
        Ap(func, arg)
end


reduc(Ap(Lam(LocalVar(1)), Prod([FreeVar("50")])))
Ap(Ap(Lam(Lam(LocalVar(1))), Prod([FreeVar("50")])), Prod([FreeVar("100")])) |> reduc |> pr

reduc(Ap(Lam(LocalVar(1)), Prod([FreeVar("50"), FreeVar("100")])))
reduc(Ap(BaseVal(2), Prod([LocalVar(2), FreeVar("5")])))
reduc(Ap(Lam(Ap(BaseVal(2), LocalVar(1))), Prod([Prod([LocalVar(2), FreeVar("5")])])))


# EXAMPLE/ Test/ goal:

# encode Map
v = Prod([Sum(Prod([FreeVar("a")]), 1), Sum(Prod([FreeVar("b")]), 2), Sum(Prod([FreeVar("c")]), 1), Sum(Prod([FreeVar("d")]), 2)])
vv = Lam(Ap(LocalVar(1), v))
Ap(vv, Prod([BaseVal(2)])) |> reduc |> pr

# a generic function
f = Match([Lam(FreeVar("Z")), Lam(LocalVar(1))])

hh_simple = Lam(Ap(LocalVar(1), Ap(LocalVar(2), LocalVar(3))))  # YES, if _1 is a match and (_3 ._2) is a prod this won't work: but: this whole thing will require type checking ANYWAY, even with lambdas, so u stfu.
hh_simple |> pr

hh_simple_partApp = Lam(Ap(hh_simple, Prod([f, vv, Prod([LocalVar(1)])]))) |> reduc
hh_simple_partApp |> pr

[1, 2,3, 4] .|> (x->reduc(Ap(hh_simple_partApp, Prod([BaseVal(x)]))) ) .|> pr


# You want partial application? Here's partial application:
# this function takes a function of 3 arguments and a term, and applies the term as SECOND argument, returning a normalized down function:
part = Lam(Partial(LocalVar(1), Prod([NewLocVar(1), LocalVar(2), NewLocVar(2)])))
# OR:
part_applied_f = Lam(Ap(f, Prod([LocalVar(1), arg, LocalVar(2)])))


# currently it CAN go into a loop because it isn't type checked:
l = Lam(Ap(LocalVar(1), Prod([LocalVar(1)])))
Ap(l, Prod([l])) |> reduc


# GOAL now: the idea is that this: x .f .(g<y>) .h  
# MUST BE ABLE to become this ( that doesn't need paranthesis): [y, x .f] .g .h
# YES this is currying, i never said it wasn't. The NewLocVar IMPLEMENTAION of Partial should support it naturallt, tho 

Ap(FreeVar("h"), 
   Ap(FreeVar("g"), Prod([LocalVar("y"), NewLocVar(1)])),
   FreeVar("f"),
   LocalVar("x")
   )

# becomes:
Ap(FreeVar("h"), Prod([Ap(FreeVar("g"), 
    Prod([LocalVar("y"), Ap(FreeVar("f"), Prod([LocalVar("x")]) )])
)]))


########################################################################## types:

struct Pi <: Term
    from::Term
    to::Term
end
pr(x::Pi)::String = "($(pr(x.from))->$(pr(x.to)))" 


build_FreeVar(x::FreeVar)::FreeVar = FreeVar(x)
build_BaseVal(x::BaseVal)::BaseVal = BaseVal(x)
build_LocalVar(x::LocalVar)::LocalVar = LocalVar(x)
build_Uni(x::Uni)::Uni = Uni(x)
build_Ap(x::Ap)::Ap = Ap(x)
build_Lam(x::Lam)::Lam = Lam(x)
build_Pi(x::Pi)::Pi = Pi(x)
build_Prod(x::Prod)::Prod = Prod(x)
build_Sum(x::Sum)::Sum = Sum(x)
build_Match(x::Match)::Match = Match(x)
