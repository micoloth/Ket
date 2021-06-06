
Index = Int
Id = String
Error = String

abstract type Expr end
abstract type Type_ end
abstract type ContextElem end

Context = Array{ContextElem}

########## Expres

struct EGlob <: Expr
    n::Id 
    type::Type_ # Type_ ???
end
struct ELoc <: Expr n::Index end
struct EUnit <: Expr end
struct EApp <: Expr
    func::Expr # must compute to a lambda
    arg::Expr # must compute to a PROD
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

struct TGlob <: Type_  
    var::Id 
end
struct TLoc <: Type_ 
    var::Index 
end
struct TUnit <: Type_ end
struct TExists <: Type_
    var::Index # this is ACTUALLY A METAVARIABLE, I'm fairly sure now...
end
struct TForall <: Type_
    body::Type_ # idea: this CAN contain (type level) local variables
end
struct TFun <: Type_
    inputs::Type_ # must compute to a PROD
    t2::Type_
end
struct TProd <: Type_
    data::Array{Type_}
end
Base.:(==)(a::TProd, b::TProd) = Base.:(==)(a.data, b.data)
Base.:(==)(a::TFun, b::TFun) = Base.:(==)(a.inputs, b.inputs) & Base.:(==)(a.t2, b.t2)
Base.:(==)(a::TForall, b::TForall) = Base.:(==)(a.body, b.body)

pr(x::EGlob)::String = "$(x.n)"#: $(pr(x.type))"
pr(x::ELoc)::String = "$(x.n)"
pr(x::EUnit)::String = "T" 
# pr(x::EApp)::String = "(" * pr(x.arg) * " ." * pr(x.func) *")" # join(x.func .|> pr, ".")
pr(x::EApp)::String = (arg = length(x.arg.data)!=1 ? (x.arg |> pr) : (x.arg.data[1] |> pr); pr(x.func) * "(" * arg * ")")
pr(x::EAbs)::String = "/{$(pr(x.body))}" 
pr(x::EProd)::String = "[$(join(x.data .|> pr, ", ")),]" 
pr(x::EAnno)::String = "($(pr(x.expr)):$(pr(x.type)))" 


subst(news::Array{Expr}, t::EGlob)::Expr= t 
subst(news::Array{Expr}, t::ELoc)::Expr = if t.n <= length(news) news[t.n] else throw(DomainError("Undefined local var $(t.n), n args given = $(length(news))" )) end
subst(news::Array{Expr}, t::EUnit)::Expr = t 
subst(news::Array{Expr}, t::EApp)::Expr = EApp(subst(news, t.func), subst(news, t.arg)) 
subst(news::Array{Expr}, t::EAbs)::Expr = t # EAbs(subst(news, t.body)) 
subst(news::Array{Expr}, t::EAnno)::Expr = EAnno(subst(news, t.expr), t.type) 
subst(news::Array{Expr}, t::EProd)::Expr = EProd(t.data .|> (x->subst(news, x))) 

reduc(t::EGlob)::Expr = t
reduc(t::ELoc)::Expr = t
reduc(t::EUnit)::Expr = t
reduc(t::EAbs)::Expr = EAbs(reduc(t.body))
reduc(t::EApp)::Expr = (t|>pr|>println; reduc(reduc(t.func), reduc(t.arg))) # EApp is AN OBJECT THAT REPRESENTS A COMPUTATION (it's only "reduc" here since which one is "typechecked at runtime")
reduc(t::EProd)::Expr = EProd(t.data .|> reduc)
reduc(t::EAnno)::Expr = EAnno(t.expr |> reduc, t.type)
function reduc(func::EAbs, arg::EProd)
    #println("> doing the ", typeof(func),  " ", typeof(arg), " thing")
    temp = subst(arg.data, func.body)
    #println( "creating  > ", temp|>pr, "\n")
    reduc(temp)
end
function reduc(func, arg)
    #println("> STOP, since apparently they are ", typeof(func),  " ", typeof(arg), " ...")
    EApp(func, arg)
end

# small helper funcs
EAppAuto(x, y) = EApp(x, EProd([y]))
EGlobAuto(n::Id) = EGlob(n, TGlob(uppercase(n)))

S = EAbs(EAppAuto(EAppAuto(ELoc(1), ELoc(3)), EAppAuto(ELoc(2), ELoc(3))))
pr(S)

reduc(EAbs(EApp(S, EProd([EGlobAuto("f"), EGlobAuto("g"), EGlobAuto("x")])))) |> pr

f = EAbs(ELoc(1))
g = EAbs(EGlobAuto("y"))
reduc(EApp(S, EProd([f, g, EGlobAuto("x")]))) |> pr


# NOT used by the above:
arity(base::Index, t::EGlob)::Index= base 
arity(base::Index, t::ELoc)::Index = max(base, t.n)
arity(base::Index, t::EUnit)::Index = base 
arity(base::Index, t::EApp)::Index = max(arity(base, t.func), arity(base, t.arg)) 
arity(base::Index, t::EAbs)::Index = base # Lam(arity(base, t.body)) 
arity(base::Index, t::EProd)::Index = reduce(max, t.data .|> (x->arity(base, x))) 
arity(base::Index, t::EAnno)::Index = arity(base, t.expr)
arity(t::Expr)::Index = arity(0, t)


# Type functions 


TFunAuto(x, y) = TFun(TProd([x]), y)


pr(x::TGlob)::String = "$(x.var)"
pr(x::TLoc)::String = "T$(x.var)"
pr(x::TUnit)::String = "UU"
pr(x::TExists)::String = "∃$(x.var)"
pr(x::TForall)::String = "∀($(x.body |> pr))"
pr(x::TFun)::String = ( arg = ((!(x.inputs isa TProd)) | (length(x.inputs.data)!=1)) ? (x.inputs |> pr) : (x.inputs.data[1] |> pr); "($(arg)->$(x.t2|>pr))" )
pr(x::TProd)::String = "[$(join(x.data .|> pr, " x "))]" 

subst(news::Array{Type_}, t::TGlob)::Type_= t 
subst(news::Array{Type_}, t::TLoc)::Type_ = if t.var <= length(news) news[t.var] else throw(DomainError("Undefined local var $(t.var), n args given = $(length(news))" )) end
subst(news::Array{Type_}, t::TUnit)::Type_ = t 
subst(news::Array{Type_}, t::TFun)::Type_ = TFun(subst(news, t.inputs), subst(news, t.t2)) 
subst(news::Array{Type_}, t::TForall)::Type_ = t # TForall(subst(news, t.body)) 
subst(news::Array{Type_}, t::TProd)::Type_ = TProd(t.data .|> (x->subst(news, x))) 
subst(news::Array{Type_}, t::TExists)::Type_ = t

reduc(t::TGlob)::Type_ = t
reduc(t::TLoc)::Type_ = t
reduc(t::TUnit)::Type_ = t
reduc(t::TForall)::Type_ = TForall(reduc(t.body))
reduc(t::TFun)::Type_ = (t|>pr|>println; reduc(reduc(t.inputs), reduc(t.t2))) # EApp is AN OBJECT THAT REPRESENTS A COMPUTATION (it's only "reduc" here since which one is "typechecked at runtime")
reduc(t::TProd)::Type_ = TProd(t.data .|> reduc)
reduc(t::TExists)::Type_ = t
function reduc(func::TForall, arg::TProd)
    #println("> doing the ", typeof(func),  " ", typeof(arg), " thing")
    temp = subst(arg.data, func.body)
    #println( "creating  > ", temp|>pr, "\n")
    reduc(temp)
end
function reduc(func, arg)
    #println("> STOP, since apparently they are ", typeof(func),  " ", typeof(arg), " ...")
    EApp(func, arg)
end

# NOT used by the above:
arity(base::Index, t::TGlob)::Index= base 
arity(base::Index, t::TLoc)::Index = max(base, t.var)
arity(base::Index, t::TUnit)::Index = base 
arity(base::Index, t::TFun)::Index = max(arity(base, t.inputs), arity(base, t.t2)) 
arity(base::Index, t::TForall)::Index = base # Lam(arity(base, t.body)) 
arity(base::Index, t::TExists)::Index = base
arity(base::Index, t::TProd)::Index = reduce(max, t.data .|> (x->arity(base, x))) 
arity(t::Type_)::Index = arity(0, t)

EGlob("x", TGlob("A"))
EAnno(ELoc(1), TFunAuto(TGlob("A"), TGlob("B")))
EAnno(ELoc(2), TExists(1))

SType1 = TFunAuto(TGlob("X"), TGlob("A"))
SType2 = TFunAuto(TGlob("X"), TFunAuto(TGlob("A"), TGlob("B")))
SType = TFun(TProd([SType2, SType1, TGlob("X")]), TGlob("B"))

@assert SType |> pr == "([(X->(A->B)) x (X->A) x X]->B)"

EGlob("S", TFunAuto(TGlob("A"), TGlob("B"))) |> pr

# Now polymorphicly:
SType1P = TFunAuto(TLoc(3), TLoc(2))
SType2P = TFunAuto(TLoc(3), TFunAuto(TLoc(2), TLoc(1)))
STypeP = TForall(TFun(TProd([SType2P, SType1P, TLoc(3)]), TLoc(1)))

@assert STypeP |> pr == "∀(([(T3->(T2->T1)) x (T3->T2) x T3]->T1))"


########## Context elements:

struct CForall <: ContextElem end # PLACEHOLDER, also called ANY TYPE.
# The Tvar referring to this position can be ANY TYPE.
# Does this IMPLICITELY DEFINE A FUNCTION SCOPE ON THE FOLLOWING???
# ^ originally had a Tvar
struct CVar <: ContextElem
    type::Type_ # type (annotation) of the VAR (NOT Tvar) referring to this position. 
end
struct CExists <: ContextElem end # difference w/ CForall ??? # the difference is: this is WAITING to be solved, i think
struct CExistsSolved <: ContextElem
    type::Type_ # type (meaning) of the Tvar referring to this position.
end
# struct CMarker <: ContextElem end # K now i'm lost. "scoping reasons", he says

pr(c::CForall) = "CForall()"
pr(c::CVar) = "CVar($(c.type|>pr))"
pr(c::CExists) = "CExists()"
pr(c::CExistsSolved) = "CExistsSolved($(c.type|>pr))"

# i REALLY wish i didn't need these :(
# what these do is: they DEREFERENCE ALL TExists IN THE GAMMA, returning the RESULTING Type_ IF solved, or TExist again if unsolved
# (they are LITERALLY just subst, but for Context/Exists, in other words)
apply(gamma:: Context, typ::TUnit)::Type_ = typ
apply(gamma:: Context, typ::TGlob)::Type_ = typ
apply(gamma:: Context, typ::TLoc)::Type_ = typ
apply(gamma:: Context, typ::TForall)::Type_ = TForall(apply(gamma, typ.body))
apply(gamma:: Context, typ::TProd)::Type_ = TProd(typ.data .|> (x->apply(gamma, x)))
apply(gamma:: Context, typ::TFun)::Type_ = TFun(apply(gamma, typ.inputs), apply(gamma, typ.t2))
function apply(gamma:: Context, typ::TExists)::Type_
    # the IDEA would be that this includes findSolved, idk if this turning a O(x) into O(0) means i'm missing something....
    if  typ.var > length(gamma)
        throw(DomainError("Undefined local var $(typ.var), n args given = $(length(gamma)) in $(gamma)"))
    elseif !(gamma[typ.var] isa CExistsSolved || gamma[typ.var] isa CExists)
        throw(DomainError("Wrong u lil shit, how can you not know, $(typ.var), should point to a CExists or CExistsSolved in this gamma with $(length(gamma)) elems: $(gamma)"))
    elseif gamma[typ.var] isa CExistsSolved
        apply(gamma, gamma[typ.var].type)
    else
        typ
    end
end
apply(gamma:: Context, typ::TUnit, lev_to_start_from:: Index)::Type_ = typ
apply(gamma:: Context, typ::TGlob, lev_to_start_from:: Index)::Type_ = typ
apply(gamma:: Context, typ::TLoc, lev_to_start_from:: Index)::Type_ = typ
apply(gamma:: Context, typ::TForall, lev_to_start_from:: Index)::Type_ = TForall(apply(gamma, typ.body, lev_to_start_from))
apply(gamma:: Context, typ::TProd, lev_to_start_from:: Index)::Type_ = TProd(typ.data .|> (x->apply(gamma, x, lev_to_start_from)))
apply(gamma:: Context, typ::TFun, lev_to_start_from:: Index)::Type_ = TFun(apply(gamma, typ.inputs, lev_to_start_from), apply(gamma, typ.t2, lev_to_start_from))
function apply(gamma:: Context, typ::TExists, lev_to_start_from:: Index)::Type_
    # the IDEA would be that this includes findSolved, idk if this turning a O(x) into O(0) means i'm missing something....
    if typ.var < lev_to_start_from
        typ
    elseif  typ.var > length(gamma)
        throw(DomainError("Undefined local var $(typ.var), n args given = $(length(gamma))"))
    elseif !(gamma[typ.var] isa CExistsSolved || gamma[typ.var] isa CExists)
        throw(DomainError("Wrong u lil shit, $(typ.var), should point to a CExists or CExistsSolved in $(length(gamma)), how can you not know"))
    elseif gamma[typ.var] isa CExistsSolved
        apply(gamma, gamma[typ.var].type,lev_to_start_from)
    else
        typ
    end
end
# QUESTION: i COULD rework this^ into a thing that REMOVES the solved ones from the context too, PROPERLY taking care of all he following TExists, BUT:
# Is this what i want? And if yes, always?   # -> What if the solved type is long and complex? We like references, don't we?

apply(Context([CExistsSolved(TGlob("G"))]), TExists(1))

monotype(t::TUnit)::Bool = true # so yes, in its weird way
monotype(t::TGlob)::Bool = true # so yes
monotype(t::TLoc)::Bool = true # so yes
monotype(t::TForall)::Bool = false # so no
monotype(t::TExists)::Bool = true # so yes
monotype(t::TFun)::Bool = monotype(t.inputs) & monotype(t.t2)
monotype(t::TProd)::Bool = t.data .|> monotype |> all

@assert monotype(TProd([TLoc(1), TExists(2), TFunAuto(TGlob("F"), TExists(3))])) == true
@assert monotype(TProd([TLoc(1), TExists(2), TFunAuto(TGlob("F"), TForall(TLoc(1)))])) == false

function solve(gamma::Context, alpha::Index, tau::Type_)::Union{Context, Nothing}
    # important: tau was a MONOTYPE i.e. not a forall
    if typeof(gamma[alpha]) === CExistsSolved
        println("Why are you trying to solve already solved $(gamma[alpha].type |>pr) in $(gamma) ???")
        return nothing
    elseif typeof(gamma[alpha]) !== CExists
        throw(DomainError("Why are you trying to solve the context elem $(gamma[alpha]) in $(gamma) ???"))
    end    
    gamma2 = copy(gamma)
    gamma2[alpha] = CExistsSolved(tau)
    # sometimes it should return nothing, too ?  (original does typewf(gamma[1:alpha-1], tau))
    # REF: typewf(gamma::Context, t::TExists_)::Bool = t.var in existentials(gamma)
    return gamma2
end

function instantiateR(gamma::Context, a::Type_, alpha::Index)::Context
    solved_gamma = monotype(a) ? solve(gamma, alpha, a) : nothing # solve CAN return nothing, too
    (solved_gamma !== nothing) ? solved_gamma : instantiateR_(gamma, a, alpha)
end
function instantiateL(gamma::Context, alpha::Index, a::Type_)::Context
    solved_gamma = monotype(a) ? solve(gamma, alpha, a) : nothing # solve CAN return nothing, too
    (solved_gamma !== nothing) ? solved_gamma : instantiateL_(gamma, alpha, a)
end

# ALL the followings are, in reality, ONLY USED BY FORALL'S:
# function instantiateR_(gamma::Context, t::TExists, alpha::Index)::Context  #IMPORTANT: Polytype
#     if (alpha != t.var) & (alpha <= length(gamma)) & (typeof(gamma[alpha]) in [CExists, CExistsSolved])
#         # ^ this is what the "ordered" function SOUNDS like, idk tho
#         solve(gamma, t.var, TExists(alpha)) # should be ALWAYS NOT NOTHING
#     else
#         solve(gamma, alpha, TExists(t.var)) # should be ALWAYS NOT NOTHING
#     end
# end
# function instantiateR_(gamma::Context, t::TFun, alpha::Index)::Context  #IMPORTANT: Polytype
#     lgamma = length(gamma)
#     theta = vcat(gamma, [CExists(), CExists()])
#     # ---------------------------------------------------------------------------------------------- BAD- PROBLEMATIC
#     theta[alpha] = CExistsSolved(TFun(TExists_(lgamma + 1), TExists_(lgamma + 2)))
#     # ^ i am NOT renaming all the TLoc's here, but i AM breaking the left-to-right logical dependency, by adding the CExists's at the end. IS THIS BAD OR NOT??
#     # ---------------------------------------------------------------------------------------------- BAD- PROBLEMATIC
#     theta = instantiateL(theta, lgamma + 1, t.inputs)
#     instantiateR(theta, apply(theta, t.t2), lgamma + 2)
# end
# function instantiateR_(gamma::Context, t::TForall, alpha::Index)::Context  #IMPORTANT: Polytype
#     # # -- Do alpha conversion to avoid clashes
#     # beta2 = newvar()
#     # beta2_c = CMarker_{Incomplete()}(beta2)
#     # l = instantiateR(Context(vcat(gamma.elements, [beta2_c, CExists_(beta2)])), typeSubst(TExists(beta2), t.arg, t.body), alpha)
#     # dropMarker(beta2_c, l)
#     println("CURRENTLY BROKEN")
#     "CURRENTLY BROKEN"
# end
# instantiateR_(gamma::Context, t, alpha::Index)::Union{Error, Context} = Error("The impossible happened! instantiateL: $(repr(alpha)), $(repr(t))")




err(alpha, alpha2) = Error("subtype, isn't subtypable: $(repr(alpha)), $(repr(alpha2))")

subtype(gamma::Context, alpha::TLoc, alpha2::TLoc)::Union{Context, Error} = ((alpha == alpha2) ? gamma : err(alpha, alpha2))
subtype(gamma::Context, alpha::TGlob, alpha2::TGlob)::Union{Context, Error} = ((alpha == alpha2) ? gamma : err(alpha, alpha2))
subtype(gamma::Context, alpha::TUnit, alpha2::TUnit)::Union{Context, Error} = gamma
subtype(gamma::Context, fa::TFun, fb::TFun)::Union{Context, Error} = (c=subtype(gamma, fb.inputs, fa.inputs); (c isa Error) ? c : subtype(c, apply(c, fa.t2), apply(c, fb.t2)))
function subtype(gamma::Context, t1::TProd, t2::TProd)::Union{Context, Error}
    for (d1, d2) in zip(t1.data, t2.data)
        gamma = subtype(gamma, d1, d2)
        if gamma === nothing return nothing end
    end
    gamma
end

# the ORIGINAL FUNCTIONS:
# subtype(gamma::Context, t::TExists, a)::Union{Context, Error} = (typeof(gamma[t.var]) in [CExists, CExistsSolved] ) ? instantiateL(gamma, t.var, a) : err(t,a)
# subtype(gamma::Context, a, t::TExists)::Union{Context, Error} = (typeof(gamma[t.var]) in [CExists, CExistsSolved]) ? instantiateR(gamma, a, t.var) : err(a,t)
# subtype(gamma::Context, alpha::TExists, alpha2::TExists) = ((alpha == alpha2) && typeof(gamma[alpha.var]) in [CExists, CExistsSolved]) ? gamma : err(alpha, alpha2)
# MY ATTEMPT at being more flexible (it will be tragic i know):
function subtype(gamma::Context, t::TExists, a)::Union{Context, Error}
    if gamma[t.var] isa CExists
        instantiateL(gamma, t.var, a) 
    elseif gamma[t.var] isa CExistsSolved
        subtype(gamma, gamma[t.var].type, a) # REAALY sounds innocuous doesn't it?
    else
        err(t,a)
    end
end
function subtype(gamma::Context, a, t::TExists)::Union{Context, Error}
    if gamma[t.var] isa CExists
        instantiateR(gamma, a, t.var) 
    elseif gamma[t.var] isa CExistsSolved
        subtype(gamma, a, gamma[t.var].type) # REAALY sounds innocuous doesn't it?
    else
        err(a, t)
    end
end
function subtype(gamma::Context, alpha::TExists, alpha2::TExists)::Union{Context, Error}
    if (alpha == alpha2) gamma  # typeof(gamma[alpha.var]) in [CExists, CExistsSolved]) 
    elseif (gamma[alpha.var] isa CExists) instantiateR(gamma, alpha, alpha2.var) # could SO EASILY be L
    elseif (gamma[alpha2.var] isa CExists) instantiateL(gamma, alpha.var, alpha2) # could SO EASILY be R
    else err(alpha, alpha2)
    end
end

@assert subtype(Context([]), TGlob("G"), TGlob("G")) == Context([])
@assert subtype(Context([]), TLoc(3), TLoc(3)) == Context([])
@assert subtype(Context([CExistsSolved(TGlob("G"))]), TGlob("G"), TExists(1)) == Context([CExistsSolved(TGlob("G"))])
# ^ MAYBE trying to solve an ALREADY SOLVED Exists is NEVER a thing... ^ ok no but WHY WOULDNT it.....
# to be fair, it DOESN'T happen in typecheck, as apply() happens FIRST
@assert subtype(Context([CExistsSolved(TGlob("G"))]), TGlob("F"), TExists(1)) == "subtype, isn't subtypable: TGlob(\"F\"), TGlob(\"G\")"
@assert subtype(Context([CExistsSolved(TGlob("G"))]), TExists(1), TGlob("G")) == Context([CExistsSolved(TGlob("G"))])


function subtype(gamma::Context, a, t::TForall) # R: more subtle, contxt is EXTENDED with the loc?
    lgamma, ltyp = length(gamma), t.body |> arity # we DON'T want this to exist :(
    gamma2 = vcat(gamma, [CForall() for i in 1:ltyp])
    sbody = subst(Array{Type_}([TLoc(lgamma + i) for i in 1:ltyp]), t.body)
    gamma_res = subtype(gamma2, a, sbody)
    # dropMarker(vc, gamma_res)  # i don't know how to drop U_U
    gamma_res
end
function subtype(gamma::Context, a::TForall, t::TForall) # the same PREVIOUS case
    lgamma, ltyp = length(gamma), t.body |> arity # we DON'T want this to exist :(
    gamma2 = vcat(gamma, [CForall() for i in 1:ltyp])
    sbody = subst(Array{Type_}([TLoc(lgamma + i) for i in 1:ltyp]), t.body)
    gamma_res = subtype(gamma2, a, sbody)
    # dropMarker(vc, gamma_res)  # i don't know how to drop U_U
    gamma_res
end
function subtype(gamma::Context, t::TForall, b) # L: Turn Forall loc's into Exists, then solve
    lgamma, ltyp = length(gamma), t.body |> arity # we DON'T want this to exist :(
    gamma2 = vcat(gamma, [CExists() for i in 1:ltyp])
    sbody = subst(Array{Type_}([TExists(lgamma + i) for i in 1:ltyp]), t.body)
    gamma_res = subtype(gamma2, sbody, b)
    # dropMarker(vc, gamma_res)  # i don't know how to drop U_U
    println("Getting to context: ", gamma_res)
    (gamma_res isa Error) ? gamma_res : gamma_res[1:lgamma]
end

subtype(gamma::Context, a, b) = Error("subtype, don't yet know what to do with: $(repr(a)), $(repr(b)) in $(gamma)")


# L case
@assert subtype(Context([]), TForall(TLoc(1)), TGlob("G")) == Context([])
@assert subtype(Context([]), TForall(TLoc(1)), TFunAuto(TGlob("A"), TGlob("B"))) == Context([])
@assert subtype(Context([]), TForall(TGlob("G")), TGlob("G")) == Context([])
@assert subtype(Context([]), TForall(TGlob("F")), TGlob("G")) == "subtype, isn't subtypable: TGlob(\"F\"), TGlob(\"G\")"
@assert subtype(Context([]), TForall(TFunAuto(TLoc(1), TLoc(2))), TFunAuto(TGlob("A"), TGlob("B"))) == Context([])
@assert subtype(Context([CExists()]), TForall(TExists(1)), TGlob("A")) == Context([CExistsSolved(TGlob("A"))])
@assert subtype(Context([CExists()]), TForall(TFunAuto(TLoc(1), TExists(1))), TFunAuto(TGlob("A"), TGlob("B"))) == Context([CExistsSolved(TGlob("B"))])


# R case
subtype(Context([]), TGlob("G"), TForall(TLoc(1)))
subtype(Context([]), TGlob("G"), TForall(TGlob("G")))
subtype(Context([]), TGlob("G"), TForall(TGlob("F")))
# subtype(Context([CExists()]), TExists(1), TForall(TExists(1)))

subtype(Context([]), TForall(TGlob("F")), TForall(TLoc(1)))
subtype(Context([]), TForall(TLoc(1)), TForall(TGlob("F")))


# -- | Type checking:
# --   typecheck Γ e A = Δ <=> Γ |- e <= A -| Δ


TypecheckRes = Union{Error, Context}
TypesynthRes = Union{Error, Tuple{Type_, Context}}


function typecheck(gamma::Context, expr::EUnit, typ::TUnit)::TypecheckRes
    gamma
end

@assert typecheck(Context([CForall()]), EUnit(), TUnit()) == Context([CForall()])


function typecheck(gamma::Context, expr, typ::TForall)::TypecheckRes
    lgamma, ltyp = length(gamma), typ.body |> arity # we DON'T want this to exist :(
    res = typecheck(
        vcat(gamma, [CForall() for i in 1:ltyp]), 
        expr,
        subst(Array{Type_}([TLoc(i + lgamma) for i in 1:ltyp]), typ.body))
    (typeof(res) !== Error) ? res[1:lgamma] : res
end

@assert typecheck(Context([]), EUnit(), TForall(TForall(TUnit()))) == Context([])

function typecheck(gamma::Context, expr::EAbs, typ::TFun)::TypecheckRes
    lgamma, lexpr = length(gamma), expr.body |> arity # we DON'T want this to exist
    if lexpr > length(typ.inputs.data) return Error("$(expr |> pr) has too many vars to be of type $(typ |> pr) (the first has $(lexpr) vars, the second $(length(typ.inputs.data)))") end
    res = typecheck(
        vcat(gamma, [CVar(t) for t in typ.inputs.data]), 
        subst(Array{Expr}([ELoc(i + lgamma) for i in 1:lexpr]), expr.body),
        typ.t2)
    (typeof(res) !== Error) ? res[1:lgamma] : res
end
# function typecheck(gamma::Context, expr::EAbs, typ::TFunPoly)::TypecheckRes
    # How different????????
    
@assert typecheck(Context([]), EAbs(EUnit()), TFunAuto(TForall(TUnit()), TUnit())) == Context([])
# IMPORTANT NOTE: it DOES NOT return the ASSUMPTION WITHIN THE body    


function typesynth(gamma::Context, expr::EGlob)::TypesynthRes 
    (expr.type, gamma)
end

function typesynth(gamma::Context, expr::ELoc)::TypesynthRes 
    if expr.n > length(gamma)
        throw(DomainError("Undefined local var $(expr.n), n args given = $(length(gamma))"))
    elseif !(gamma[expr.n] isa CVar)
        Error("typesynth: ELoc not pointing to CVar: var $(expr), in $(gamma)")
    else
        (gamma[expr.n].type, gamma)
    end
end

function typesynth(gamma::Context, expr::EAnno)::TypesynthRes 
    tc = typecheck(gamma, expr.expr, expr.type)
    (typeof(tc) !== Error) ? (expr.type, tc) : tc 
end

function typesynth(gamma::Context, expr::EProd)::TypesynthRes 
    types = Array{Type_}([])
    for e in expr.data
        res = typesynth(gamma, e)
        if res isa Error return res end
        (t, gamma) = res
        push!(types, t)
    end
    (TProd(types), gamma)
end


function typecheck(gamma::Context, expr, typ)::TypecheckRes
    # this is good
    res = typesynth(gamma, expr)
    if (typeof(res) === Error) return res end
    (a, theta) = res
    # subtype(theta, apply(theta, a), apply(theta, typ)) # <------------ THING
    a2, typ2 = apply(theta, a), apply(theta, typ)
    # println("after applying $(theta) to $(a) you get: $(a2)")
    # println("after applying $(theta) to $(typ) you get: $(typ2)")
    theta2 = subtype(theta, a2, typ2)
    if theta2 === nothing
        Error("Doesn't typecheck: $(expr |> pr) is of type $(a2 |> pr) not $(typ2 |> pr) in $(gamma)")
    elseif theta2 isa Error
        Error("Doesn't typecheck with message: $(theta2)")
    else
        theta2
    end
end

@assert typecheck(Context([]), EGlobAuto("g"), TGlob("F")) == "Doesn't typecheck with message: subtype, isn't subtypable: TGlob(\"G\"), TGlob(\"F\")"


gamma = Context([CVar(TGlob("K")), CExists()])
expr = EAbs(EGlobAuto("g"))
tc = typecheck(gamma, expr.body, TExists(2))

gamma = Context([CVar(TGlob("K")), CExists(), CExists(), CVar(TExists(2))])
@assert subst(Array{Expr}([ELoc(4)]), EAbs(ELoc(1)).body) == ELoc(4)
tc = typecheck(gamma, ELoc(4), TExists(3))
# ^ buuh :(

@assert typecheck(Context([CVar(TGlob("F"))]), ELoc(1), TGlob("F")) == Context([CVar(TGlob("F"))])
@assert typecheck(Context([CExistsSolved(TGlob("G"))]), EGlobAuto("g"), TExists(1)) == Context([CExistsSolved(TGlob("G"))])
@assert typecheck(Context([CExistsSolved(TGlob("G"))]), EGlobAuto("f"), TExists(1)) == "Doesn't typecheck with message: subtype, isn't subtypable: TGlob(\"F\"), TGlob(\"G\")"
@assert typecheck(Context([CExists()]), EGlobAuto("g"), TExists(1)) == Context([CExistsSolved(TGlob("G"))])
@assert typecheck(Context([CExists(), CVar(TLoc(1))]), ELoc(2), TExists(1)) == Context([CExistsSolved(TLoc(1)), CVar(TLoc(1))])
@assert typecheck(Context([CExistsSolved(TGlob("F")), CVar(TGlob("F"))]), EAnno(ELoc(2), TGlob("F")), TExists(1)) == Context([CExistsSolved(TGlob("F")), CVar(TGlob("F"))])
@assert typecheck(Context([CExistsSolved(TGlob("F")), CVar(TExists(1))]), EAnno(ELoc(2), TGlob("F")), TExists(1)) == Context([CExistsSolved(TGlob("F")), CVar(TExists(1))])
@assert typecheck(Context([CExists(), CVar(TExists(1))]), EAnno(ELoc(2), TGlob("F")), TExists(1)) == Context([CExistsSolved(TGlob("F")), CVar(TExists(1))])
@assert typecheck(Context([CExists(), CVar(TExists(1))]), EAnno(ELoc(2), TExists(1)), TGlob("F")) == Context([CExistsSolved(TGlob("F")), CVar(TExists(1))])
@assert typecheck(Context([CExists(), CVar(TLoc(1))]), EAnno(ELoc(2), TLoc(1)), TExists(1)) == Context([CExistsSolved(TLoc(1)), CVar(TLoc(1))])


@assert typecheck(Context([CExists(), CVar(TExists(1))]), EProd([EAnno(ELoc(2), TGlob("G")), EAnno(ELoc(2), TExists(1))]), TProd([TExists(1), TGlob("G")])) == Context([CExistsSolved(TGlob("G")), CVar(TExists(1))])
# typecheck(Context([CExists()]), EAbs(EProd())

# @assert typecheck(Context([CExists(), CVar(TExists(1))]), EAnno(ELoc(2), TLoc(1)), TExists(1)) == Context([CExistsSolved(TLoc(1)), CVar(TLoc(1))])




# -- | Type synthesising:
# --   typesynth Γ e = (A, Δ) <=> Γ |- e => A -| Δ


# function typesynth(gamma::Context, expr::ELoc)::TypesynthRes 
# function typesynth(gamma::Context, expr::EGlob)::TypesynthRes 
# Written above, for tests

typesynth(Context([CVar(TGlob("G"))]), EGlobAuto("f"))


typesynth(Context([CVar(TGlob("G"))]), ELoc(1))
typesynth(Context([CExists()]), ELoc(1))


@assert typesynth(Context([CVar(TGlob("K"))]), EAnno(EGlobAuto("g"), TGlob("G"))) == (TGlob("G"), ContextElem[CVar(TGlob("K"))])
@assert typesynth(Context([CVar(TGlob("K"))]), EAnno(EGlobAuto("f"), TGlob("G"))) == "Doesn't typecheck with message: subtype, isn't subtypable: TGlob(\"F\"), TGlob(\"G\")" # shouldn't typecheck
# typesynth(Context([CVar(TGlob("G"))]), EAnno(EGlobAuto("g"), TExists(1))) # SHOULD raise error
@assert typesynth(Context([CExistsSolved(TGlob("G"))]), EAnno(EGlobAuto("g"), TExists(1))) == (TExists(1), ContextElem[CExistsSolved(TGlob("G"))])
# ^ note that it WORKS, it just returns TExists(1) again


function typesynth(gamma::Context, expr::EUnit)::TypesynthRes 
    (TUnit(), gamma)
end


substEx(new::Type_, var::Index, expr::TUnit)::Type_ = expr
substEx(new::Type_, var::Index, expr::TLoc)::Type_ = expr
substEx(new::Type_, var::Index, expr::TGlob)::Type_ = expr
substEx(new::Type_, var::Index, expr::TProd)::Type_ = TProd(expr.data .|> (x->substEx(new, var, x)))
substEx(new::Type_, var::Index, expr::TFun)::Type_ = TFun(substEx(new, var, expr.inputs), substEx(new, var, expr.t2))
substEx(new::Type_, var::Index, expr::TExists)::Type_ = (expr.var == var ? new : expr)
# substEx(new::Type_, var::Index, expr::TForall)::Type_ = TForall(substEx(new, var, expr.body)) 
# ^it's MORE COMPLICATED than this, due to the fact that, INTO THE SCOPE, Loc's HAVE A MEANING already...


function typesynth(gamma::Context, expr::EAbs)::TypesynthRes 
    lgamma, lexpr = length(gamma), expr.body |> arity
    alphas = [CExists() for i in 1:lexpr] 
    x2s = [CVar(TExists(lgamma + i)) for i in 1:lexpr] # x2:alpha
    texists = [TExists(lgamma + i) for i in 1:lexpr] # pointing to alphas
    # positions where x2's end up: lgamma + lexpr + 1 + 1 tolgamma + lexpr + 1 + lexpr
    newlocs = [ELoc(lgamma + lexpr + 1 + i) for i in 1:lexpr] 
    beta = TExists(lgamma + lexpr + 1)

    delta = vcat(gamma, alphas, [CExists()], x2s) # alphaS, beta, vars
    a2 = subst(Array{Expr}(newlocs), expr.body) # var of type alpha   
    # but isn't just alpha enough????????? -> I'm going with NO, now!! (because you would lose EQUALITY, i dunno if it's a thing)
    tc = typecheck(delta, a2, beta)

    # SIMPLER/ ORIGINAL
    #return (typeof(tc) === Error) ? tc : (TFun(TProd(texists), beta), tc)
    
    # FULL Damas-Milner
    # -- ->I=> Full Damas-Milner type inference
    # are we just assuming it's never an error?
    @assert (! (tc isa Error)) tc

    # IDEA: first 1. you APPPLY all (TExists pointing to) CExistsSolved's directly into return type, second 2. you Turn all REMAINING (TExists pointing to) CExist's into TLoc's !!!

    #1.
    # idea: rn left-to-right dependencies are BROKEN, but EVEN IN THE WORST CASE, i'm NEVER doing the thing of 
    # CHANGING WHAT COMES BEFORE...
    # SO, lgamma is a GOOD INFORMATION about where to split!!!
    texists = [TExists(i + lgamma) for i in 1:lexpr] # pointing to alphas IN delta2 
    beta = TExists(lexpr + lgamma + 1)
    #^ yes right, the equivalent ones above are superfluous // OK no problem at all w/ texists, but beta ????
    tau = apply(tc, TFun(TProd(texists), beta), lgamma+1)
    
    (delta, delta2) = tc[1:lgamma], tc[lgamma+1:end]
    #2.
    evars = [i + lgamma for (i, c) in enumerate(delta2) if c isa CExists]
    for (i_newloc, i_exists) in enumerate(evars)
        tau = substEx(TLoc(i_newloc), i_exists, tau)
    end
    return (TForall(tau), delta)# or tc? Don't think gamma...
end


typesynth(Context([CVar(TGlob("K"))]), EAbs(EGlobAuto("g")))
gamma = Context([CVar(TGlob("K"))])
expr = EAbs(ELoc(1))
@assert typesynth(gamma, expr) == (TForall(TFun(TProd(Type_[TLoc(1)]), TLoc(1))), ContextElem[CVar(TGlob("K"))]) 

@assert typesynth(Context([CVar(TGlob("K"))]), EAbs(EAnno(ELoc(1), TGlob("A")))) == (TForall(TFun(TProd(Type_[TGlob("A")]), TGlob("A"))), ContextElem[CVar(TGlob("K"))])

@assert typesynth(Context([]), EAnno(EAbs(EProd([ELoc(1), EGlobAuto("g")])), TForall(TFunAuto(TLoc(1), TProd([TLoc(1), TGlob("G")]))))) == (TForall(TFun(TProd([TLoc(1)]), TProd([TLoc(1), TGlob("G")]))), ContextElem[])
c = Context([CExists()])
e = EAnno(EAbs(EProd([ELoc(1), EGlobAuto("g")])), TForall(TFunAuto(TLoc(1), TProd([TLoc(1), TExists(1)]))))
@assert typesynth(c, e) == (TForall(TFun(TProd(Array{Type_}([TLoc(1)])), TProd(Array{Type_}([TLoc(1), TExists(1)])))), ContextElem[CExistsSolved(TGlob("G"))])
EAnno(EAbs(EProd([ELoc(1), EGlobAuto("g")])), TForall(TFunAuto(TLoc(1), TProd([TLoc(1), TExists(1)])))) |>pr

function typesynth(gamma::Context, expr::EApp)::TypesynthRes
    res = typesynth(gamma, expr.func)
    if (typeof(res) === Error) return res end
    (a, theta) = res
    typeapplysynth(theta, apply(theta, a), expr.arg)
end

# -- | Type application synthesising
# --   typeapplysynth Γ A e = (C, Δ) <=> Γ |- A . e =>> C -| Δ

function typeapplysynth(gamma::Context, typ::TForall, expr::Expr)::TypesynthRes
    lgamma, ltyp = length(gamma), typ.body |> arity # we DON'T want this to exist :(
        typeapplysynth(
            vcat(gamma, [CExists() for i in 1:ltyp]), 
            subst(Array{Type_}([TExists(i + lgamma) for i in 1:ltyp]), typ.body),
            expr,
            )
end

function typeapplysynth(gamma::Context, typ::TExists, expr::Expr)::TypesynthRes
    lgamma = length(gamma)
    println("yep.. Definitely happing")
    #                   alpha2, alpha1
    c = vcat(gamma, [CExists(), CExists(), CExistsSolved(TFun(TExists(lgamma + 2), TExists(lgamma + 1)))])
    delta = typecheck(c, expr, TExists(lgamma + 2))
    (typeof(delta) === Error) ? delta : (TExists(lgamma + 1), delta)
end

function typeapplysynth(gamma::Context, typ::TFun, expr::Expr)::TypesynthRes
    res = typecheck(gamma, expr, typ.inputs)
    (typeof(res) === Error) ? res : (typ.t2, res)
end

function typeapplysynth(gamma::Context, typ, expr::Expr)::TypesynthRes
    Error("typeapplysynth: don't know what to do with: $(gamma), $(typ), $(expr)")
end


# Combinator S:

S = EAbs(EAppAuto(EAppAuto(ELoc(1), ELoc(3)), EAppAuto(ELoc(2), ELoc(3))))
pr(S)

reduc(EAbs(EApp(S, EProd([EGlobAuto("f"), EGlobAuto("g"), EGlobAuto("x")])))) |> pr

f = EAbs(ELoc(1))
g = EAbs(EGlobAuto("y"))
reduc(EApp(S, EProd([f, g, EGlobAuto("x")]))) |> pr

SType1 = TFunAuto(TGlob("X"), TGlob("A"))
SType2 = TFunAuto(TGlob("X"), TFunAuto(TGlob("A"), TGlob("B")))
SType = TFun(TProd([SType2, SType1, TGlob("X")]), TGlob("B"))

@assert SType |> pr == "([(X->(A->B)) x (X->A) x X]->B)"

EGlob("S", TFunAuto(TGlob("A"), TGlob("B"))) |> pr

# Now polymorphicly:
SType1P = TFunAuto(TLoc(3), TLoc(2))
SType2P = TFunAuto(TLoc(3), TFunAuto(TLoc(2), TLoc(1)))
STypeP = TForall(TFun(TProd([SType2P, SType1P, TLoc(3)]), TLoc(1)))

@assert STypeP |> pr == "∀(([(T3->(T2->T1)) x (T3->T2) x T3]->T1))"


typecheck(Context([]), S, STypeP)
typecheck(Context([]), S, SType)

S = EAbs(EAppAuto(EAppAuto(EAnno(ELoc(1), TExists(1)), EAnno(ELoc(3), TGlob("X"))), EAnno(EAppAuto(EAnno(ELoc(2),TExists(2)), ELoc(3)), TGlob("A"))))
S |> pr
SType |> pr
cres = typecheck(Context([CExists(), CExists()]), S, SType) 
println("Type of $(S |> pr) is confirmed $(SType |> pr) in context $(cres .|> pr) !!!")

tres, cres = typesynth(Context([CExists(), CExists()]), S)
println("Type of $(S |> pr) is generated $(tres |> pr) in context $(cres .|> pr) !!!")






@assert typesynth(Context([]), EAppAuto(EAbs(EProd([ELoc(1), EGlobAuto("g")])), EGlobAuto("f"))) |> (x->apply(x[2], x[1])) == TProd([TGlob("F"), TGlob("G")])
typesynth(Context([]), EAppAuto(EAbs(EProd([ELoc(1), EGlobAuto("g")])), EGlobAuto("f")))
        
@assert typesynth(Context([]), EAppAuto(EAbs(EProd([ELoc(1), EGlobAuto("g")])), EGlobAuto("f"))) |> (x->apply(x[2], x[1])) == TProd([TGlob("F"), TGlob("G")])
typesynth(Context([]), EAppAuto(EAbs(EProd([ELoc(1), EGlobAuto("g")])), EGlobAuto("f")))

typecheck(Context([]), EProd([EGlobAuto("f"), EGlobAuto("g")]), TForall(TProd([TLoc(1), TLoc(2)])))
c, e, t = Context([CExists(), CVar(TExists(1))]), EProd([ELoc(2)]), TForall(TProd([TLoc(1)]))
typecheck(c, e, t)
