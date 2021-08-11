
Index = Int
Id = String
Error = String

abstract type Expr end
abstract type Type_ end

########## Expres

struct EGlob <: Expr
    n::Id 
    type::Type_ # Type_ ???
end
struct ELoc <: Expr n::Index end
struct EUnit <: Expr end
struct EApp <: Expr
    ops_dot_ordered::Array{Expr} 
    # Each one must compute to a lambda
    # Each lambda must RETURN a PROD, but really WE WILL BE EXTREMELY GENEROUS WITH THE TYPECHECKING
    # Furthermore, the FIRST one (dot_ordered) can (should?) should be a lambda with ZERO arguments, but again, WE WILL BE EXTREMELY GENEROUS WITH THE TYPECHECKING
    # Is typechecking still what we are doing?🤔
end
struct EAbs <: Expr # lambda, for some reason
    body::Expr 
end
struct EProd <: Expr
    data::Array{Expr}
end
struct EAnno <: Expr # ANNOTATION syntax
    expr::Expr
    type::Type_ # Type_ ???
end
Base.:(==)(a::EProd, b::EProd) = Base.:(==)(a.data, b.data)


########## Types

# struct TUnit <: Type_ end
struct TTop <: Type_ end
struct TGlob <: Type_  
    var::Id 
end
struct TLoc <: Type_ 
    var::Index 
end
struct TForall <: Type_
    body::Type_ # idea: this CAN contain (type level) local variables
end
struct TApp <: Type_ # idk why they woudn't have this
    ops_dot_ordered::Array{Type_} 
    # Each one must compute to a TForall
    # Each lambda must RETURN a TPROD, but really WE WILL BE EXTREMELY GENEROUS WITH THE "TYPECHECKING"
end
struct TTerm <: Type_
    t_in::Array{Type_}  # Type of input, should be a TProd.  
    t_out::Type_  # type of the output
end
struct TProd <: Type_
    data::Array{Type_}
end
Base.:(==)(a::TProd, b::TProd) = Base.:(==)(a.data, b.data)
Base.:(==)(a::TTerm, b::TTerm) = a.typs_dot_ordered == b.typs_dot_ordered
Base.:(==)(a::TForall, b::TForall) = Base.:(==)(a.body, b.body)
Base.:(==)(a::TApp, b::TApp) = a.ops_dot_ordered == b.ops_dot_ordered


pr(x::EGlob)::String = "$(x.n)"
pr(x::ELoc)::String = "$(x.n)"
pr(x::EUnit)::String = "T" 
# pr(x::EApp)::String = "(" * pr(x.arg) * " ." * pr(x.func) *")" # join(x.func .|> pr, ".")
pr(x::EAbs)::String = "/{$(pr(x.body))}" 
pr(x::EProd)::String = "[$(join(x.data .|> pr, ", ")),]" 
pr(x::EAnno)::String = "$(pr(x.expr)):$(pr(x.type))" 
function pr(x::EApp)::String
    if length(x.ops_dot_ordered) == 2
        arg, func = x.ops_dot_ordered[1], x.ops_dot_ordered[2]
        arg = (arg isa EProd && length(arg.data)==1) ? (arg.data[1] |> pr) : (arg |> pr)
        pr(func) * "(" * arg * ")"
    elseif length(x.ops_dot_ordered) <= 1
        throw(DomainError("howw $(x)"))
    else
        x.ops_dot_ordered .|> pr |> x->join(x, ".")
    end
end


subst(news::Array{Expr}, t::EGlob)::Expr= t 
subst(news::Array{Expr}, t::ELoc)::Expr = if t.n <= length(news) news[t.n] else throw(DomainError("Undefined local var $(t.n), n args given = $(length(news))" )) end
subst(news::Array{Expr}, t::EUnit)::Expr = t 
subst(news::Array{Expr}, t::EApp)::Expr = EApp(t.ops_dot_ordered .|> x->subst(news, x)) 
subst(news::Array{Expr}, t::EAbs)::Expr = t # EAbs(subst(news, t.body)) 
subst(news::Array{Expr}, t::EAnno)::Expr = EAnno(subst(news, t.expr), t.type) 
subst(news::Array{Expr}, t::EProd)::Expr = EProd(t.data .|> (x->subst(news, x))) 

reduc(t::EGlob)::Expr = t
reduc(t::ELoc)::Expr = t
reduc(t::EUnit)::Expr = t
reduc(t::EAbs)::Expr = EAbs(reduc(t.body))
reduc(t::EApp)::Expr = (t|>pr|>println; reduc(t.ops_dot_ordered .|> reduc)) # EApp is AN OBJECT THAT REPRESENTS A COMPUTATION (it's only "reduc" here since which one is "typechecked at runtime")
reduc(t::EProd)::Expr = EProd(t.data .|> reduc)
reduc(t::EAnno)::Expr = EAnno(t.expr |> reduc, t.type)
function reduc(ops::Array{Expr})
    #println("> doing the ", typeof(func),  " ", typeof(arg), " thing")
    if ops[1] isa EAbs ops[1] = reduc(Array{Expr}([EProd([]), ops[1]])) end # this is because i still havent decided between prods and 0-arg'd lambda's. 
    #^ this MIGHT VERY WELL FAIL, idk
    while (length(ops) >= 2 && ops[1] isa EProd && ops[2] isa EAbs) ops = vcat([subst(ops[1].data, ops[2].body) |> reduc], ops[3:end]) end
    # TODO: make this into a more reasonable stack
    return length(ops) >= 2 ? EApp(ops) : ops[1]
end

# ############################## Base.getindex(a::A, i::Index) = a.a[i]

# small helper funcs
EAppSwitch(func, args) = EApp([args, func])
EAppAuto(func, args) = EApp([EProd([args]), func])
EGlobAuto(n::Id) = EGlob(n, TGlob(uppercase(n)))


S = EAbs(EAppAuto(EAppAuto(ELoc(1), ELoc(3)), EAppAuto(ELoc(2), ELoc(3))))
pr(S)

reduc(EAbs(EAppSwitch(S, EProd([EGlobAuto("f"), EGlobAuto("g"), EGlobAuto("x")])))) |> pr

f = EAbs(ELoc(1))
g = EAbs(EGlobAuto("y"))
reduc(EAppSwitch(S, EProd([f, g, EGlobAuto("x")]))) |> pr


# NOT used by the above:
arity(base::Index, t::EGlob)::Index= base 
arity(base::Index, t::ELoc)::Index = max(base, t.n)
arity(base::Index, t::EUnit)::Index = base 
arity(base::Index, t::EApp)::Index = t.ops_dot_ordered .|> arity |> maximum
arity(base::Index, t::EAbs)::Index = base # Lam(arity(base, t.body)) 
arity(base::Index, t::EProd)::Index = t.data .|> (x->arity(base, x)) |> maximum
arity(base::Index, t::EAnno)::Index = arity(base, t.expr)
arity(t::Expr)::Index = arity(0, t)


# Type functions 


TFunAuto(tin, tout) = TTerm([tin], tout)
TTermAuto(tin, tout) = TTerm([tin], tout)
TAppAuto(tfun, targ) = TApp([TProd([targ]), tfun])


subst(news::Array{Type_}, t::TGlob)::Type_= t 
subst(news::Array{Type_}, t::TLoc)::Type_ = if t.var <= length(news) news[t.var] else throw(DomainError("Undefined local var $(t.var), n args given = $(length(news))" )) end
subst(news::Array{Type_}, t::TTop)::Type_ = t 
subst(news::Array{Type_}, t::TTerm)::Type_ = TTerm(t.t_in .|> (x->subst(news, x)), subst(news, t.t_out)) 
subst(news::Array{Type_}, t::TForall)::Type_ = t # TForall(subst(news, t.body)) 
subst(news::Array{Type_}, t::TProd)::Type_ = TProd(t.data .|> (x->subst(news, x))) 
subst(news::Array{Type_}, t::TApp)::Type_ = TApp(t.ops_dot_ordered .|> x->subst(news, x)) 

reduc(t::TGlob)::Type_ = t
reduc(t::TLoc)::Type_ = t
reduc(t::TTop)::Type_ = t
reduc(t::TTerm)::Type_ = t
reduc(t::TForall)::Type_ = TForall(reduc(t.body))
reduc(t::TApp)::Type_ = reduc(t.ops_dot_ordered .|> reduc) # EApp is AN OBJECT THAT REPRESENTS A COMPUTATION (it's only "reduc" here since which one is "typechecked at runtime")
reduc(t::TProd)::Type_ = TProd(t.data .|> reduc)
function reduc(ops::Array{Type_})
    #println("> doing the ", typeof(func),  " ", typeof(arg), " thing")
    if ops[1] isa TForall ops[1] = reduc(Array{Type_}([TProd([]), ops[1]])) end # this is because i still havent decided between prods and 0-arg'd lambda's. 
    #^ this MIGHT VERY WELL FAIL, idk
    while (length(ops) >= 2 && ops[1] isa TProd && ops[2] isa TForall) ops = vcat([subst(ops[1].data, ops[2].body) |> reduc], ops[3:end]) end
    # TODO: make this into a more reasonable stack
    return length(ops) >= 2 ? TApp(ops) : ops[1]
end

pr(x::TGlob)::String = "$(x.var)"
pr(x::TLoc)::String = "T$(x.var)"
pr(x::TTop)::String = "⊥"
# pr(x::TExists)::String = "∃$(x.var)"
pr(x::TForall)::String = (arity(x.body) > 0) ? ("∀($(x.body |> pr))") : (x.body |> pr)
function pr(x::TProd)::String
    if length(x.data) == 1
        x.data[1] |> pr
    elseif length(x.data) == 0 
        "1"
    else
        "[$(join(x.data .|> pr, " x "))]" 
    end
end
function pr(x::TTerm)::String
    ins =  x.t_in .|> pr |> (x->join(x, ", "))
    ins = (length(x.t_in) ==1) ? ins : ("(" * ins * ")")
    ([ins, x.t_out|> pr]  |> x->join(x, "->")) 
end
pr(x::TApp)::String = x |>reduc |>just_pr  # Will i regret this? Yes!
just_pr(x::TApp) = x.ops_dot_ordered .|> pr .|>(x->"($(x))") |> (x->join(x, ".")) |> (x->"[Just $(x)]")
just_pr(x::Type_) = pr(x)
pr(xs::Array{Type_}) = xs .|> pr


# NOT used by the above:
arity(base::Index, t::TGlob)::Index= base 
arity(base::Index, t::TLoc)::Index = max(base, t.var)
arity(base::Index, t::TTop)::Index = base 
arity(base::Index, t::TApp)::Index = t.ops_dot_ordered .|> (x->arity(base, x)) |> maximum
arity(base::Index, t::TTerm)::Index = vcat(t.t_in, [t.t_out]) .|> (x->arity(base, x)) |> maximum
arity(base::Index, t::TForall)::Index = base # Lam(arity(base, t.body)) 
arity(base::Index, t::TProd)::Index = t.data .|> (x->arity(base, x)) |> maximum
arity(t::Type_)::Index = arity(0, t)

EGlob("x", TGlob("A"))
EAnno(ELoc(1), TFunAuto(TGlob("A"), TGlob("B")))
EAnno(ELoc(2), TForall(TLoc(1)))

SType1 = TFunAuto(TGlob("X"), TGlob("A"))
SType2 = TFunAuto(TGlob("X"), TFunAuto(TGlob("A"), TGlob("B")))
SType = TFunAuto(TProd([SType2, SType1, TGlob("X")]), TGlob("B"))


EGlob("S", TFunAuto(TGlob("A"), TGlob("B"))) |> pr
TFunAuto(TGlob("A"), TGlob("B")) |> pr

# Now polymorphicly:
SType1P = TFunAuto(TLoc(3), TLoc(2))
SType2P = TFunAuto(TLoc(3), TFunAuto(TLoc(2), TLoc(1)))
STypeP = TForall(TTerm([SType2P, SType1P, TLoc(3)], TLoc(1)))
STypeP |> pr



