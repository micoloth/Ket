
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

struct TTop <: Type_  end
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

pr(x::EGlob)::String = "$(x.n)"
pr(x::ELoc)::String = "$(x.n)"
pr(x::EUnit)::String = "T" 
# pr(x::EApp)::String = "(" * pr(x.arg) * " ." * pr(x.func) *")" # join(x.func .|> pr, ".")
pr(x::EApp)::String = (arg = length(x.arg.data)!=1 ? (x.arg |> pr) : (x.arg.data[1] |> pr); pr(x.func) * "(" * arg * ")")
pr(x::EAbs)::String = "/{$(pr(x.body))}" 
pr(x::EProd)::String = "[$(join(x.data .|> pr, ", ")),]" 
pr(x::EAnno)::String = "$(pr(x.expr)):$(pr(x.type))" 


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
pr(x::TFun)::String = ( arg = length(x.inputs.data)!=1 ? (x.inputs |> pr) : (x.inputs.data[1] |> pr); "($(arg)->$(x.t2|>pr))" )
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
SType = TFunAuto(TProd([SType2, SType1, TGlob("X")]), TGlob("B"))


EGlob("S", TFunAuto(TGlob("A"), TGlob("B"))) |> pr

# Now polymorphicly:
SType1P = TFunAuto(TLoc(3), TLoc(2))
SType2P = TFunAuto(TLoc(3), TFunAuto(TLoc(2), TLoc(1)))
STypeP = TForall(TFun(TProd([SType2P, SType1P, TLoc(3)]), TLoc(1)))



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
struct CMarker <: ContextElem end # K now i'm lost. "scoping reasons", he says

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
        throw(DomainError("Undefined local var $(typ.var), n args given = $(length(gamma))"))
    elseif !(gamma[typ.var] isa CExistsSolved || gamma[typ.var] isa CExists)
        throw(DomainError("Wrong u lil shit, $(typ.var), should point to a CExists or CExistsSolved in $(length(gamma)), how can you not know"))
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



#####################################

# abstract type ResultObj end
# struct ThingResultable <: ResultObj
#     c::Context
#     t::Type_
# end
# struct ThingResultableProd
#     data::Array{ThingResultable}
# end
# struct ThingResultableAbs
#     body::ThingResultable
# end
# struct ThingResultableApp
#     func::ThingResultable
#     arg::ThingResultable
# end

# struct ThingToTypecheck <: ResultObj
#     c::Context
#     texpr::Type_
#     t::Type_
# end


# # TypeSynth: ThingToTypeSynth -> ResultObj
# # TypeCheck: ThingToTypeCheck -> ResultObj

# makeContext(e::ELoc)::Context = [TTop() for i in 1..e.n]
# function joinContexts(Array{Context})::Context
#     Context([])
# end
# function tForallOutOfContext(c::Context, res::Type_)
#     # -> Returns res, but as a TForall where all the objs in c that res is referenceing to as turned into PARAMS.
#     # All TTop's in c are turned into T1, T2, ...
#     # res CAN refer to elems in c via TExists...
#     # So those are apply'ed away,too
#     # Finally, if TForall has resutling arity ==0, pls just return the body
# end


# typer(e::EGlob)::ResultObj = ThingResultable(Context([]), e.type)
# typer(e::ELoc)::ResultObj = ThingResultable(Context([]), TTop()) # i first thoug: # (makeContext(e), e, TExists(e.var))
# typer(e::EUnit)::ResultObj = ThingResultable(Context([]), TUnit())
# # EAnno secretly is just typer and it works automatically  # i hope
# typer(e::ThingResultableProd)::ResultObj = ThingResultable(joinContexts(e.data .|> x->x.c), TProd(e.data .|> x->x.t))
# typer(e::ThingResultableAbs)::ResultObj = ThingToTypecheck(Context([]), tForallOutOfContext(e.body.c, e.body.t)
# typer(e::ThingResultableApp)::ResultObj = typer(e.func, e.arg)

# -- | Type application synthesising
# --   typer Γ A e = (C, Δ) <=> Γ |- A . e =>> C -| Δ



#######################################################################################################


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

# ^ MAYBE trying to solve an ALREADY SOLVED Exists is NEVER a thing... ^ ok no but WHY WOULDNT it.....
# to be fair, it DOESN'T happen in typer, as apply() happens FIRST


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


# R case
subtype(Context([]), TGlob("G"), TForall(TLoc(1)))
subtype(Context([]), TGlob("G"), TForall(TGlob("G")))
subtype(Context([]), TGlob("G"), TForall(TGlob("F")))
# subtype(Context([CExists()]), TExists(1), TForall(TExists(1)))

subtype(Context([]), TForall(TGlob("F")), TForall(TLoc(1)))
subtype(Context([]), TForall(TLoc(1)), TForall(TGlob("F")))


substEx(new::Type_, var::Index, expr::TUnit)::Type_ = expr
substEx(new::Type_, var::Index, expr::TLoc)::Type_ = expr
substEx(new::Type_, var::Index, expr::TGlob)::Type_ = expr
substEx(new::Type_, var::Index, expr::TProd)::Type_ = TProd(expr.data .|> (x->substEx(new, var, x)))
substEx(new::Type_, var::Index, expr::TFun)::Type_ = TFun(substEx(new, var, expr.inputs), substEx(new, var, expr.t2))
substEx(new::Type_, var::Index, expr::TExists)::Type_ = (expr.var == var ? new : expr)
# substEx(new::Type_, var::Index, expr::TForall)::Type_ = TForall(substEx(new, var, expr.body)) 
# ^it's MORE COMPLICATED than this, due to the fact that, INTO THE SCOPE, Loc's HAVE A MEANING already...



# -- | Type checking:
# --   typer Γ e A = Δ <=> Γ |- e <= A -| Δ


TypecheckRes = Union{Error, Context}
TypesynthRes = Union{Error, Tuple{Type_, Context}}
TypingRes = Union{TypecheckRes, TypesynthRes}

###############################################################################

abstract type Typable end
abstract type Typed end

struct TypeCheckable <: Typable
    gamma::Context
    expr::Expr
    typ::Type_
end
struct TypeSynthable <: Typable
    gamma::Context
    expr::Expr
end
struct TypeAppSynthable <: Typable
    gamma::Context
    typ::Type_
    expr::Expr
end


struct TypeCheckableToClip <: Typable  # First secret Feature
    tcable::TypeCheckable
    lgamma::Index
end
struct TypeCheckableToMakeSynth <: Typable  # Second secret Feature
    type::Type_
    tcable::TypeCheckable
end
struct TypeSynthableToMakeCheck <: Typable  # Third secret Feature
    type::Type_
    tsable::TypeSynthable
end

struct ReturnTFunFlag
    lexpr::Index
    lgamma::Index
end
struct TypeCheckableToFunc <: Typable  # Fourth secret Feature
    tcable::TypeCheckable
    f::ReturnTFunFlag
end

struct TypeSynthableToMakeProd <: Typable  # Fifth secret Feature
    c::Context
    i::Int # where you at (what's the NEXT TO DO, so starts at 1)
    types::Array{Union{TypeSynthable, Type_}}
end
struct TypeSynthableToMakeApp <: Typable  # Sixth secret Feature
    func::TypeSynthable
    argToBecomeTypeCheckable::Union{TypeCheckable, Expr}
end

# struct TypeCheckedToClip <: Typed  # First secret Feature
#     tcheckRes::Context
#     lgamma::Index
# end
# struct TypeCheckedToMakeSynth <: Typed  # Second secret Feature
#     type::Type_
#     tcheckRes::Context
# end
# struct TypeSynthedToMakeCheck <: Typed  # Third secret Feature
#     type::Type_
#     tsynthResC::Context
#     tsynthResT::Type_
# end
# struct TypeCheckedToFunc <: Typed  # Fourth secret Feature
#     tcheckRes::Context
#     f::ReturnTFunFlag
# end
# struct TypeSynthedToMakeProd <: Typed  # Fifth secret feature: PARALLEL BRANCHING, PRODS
#     tsynthResC::Context
#     tsynthResTs::Array{Type_}
# end
# struct TypeSynthedToMakeApp <: Typed  # Sixth secret feature: SEQUENTIAL BRANCHING, or APP
#     typedFunc::Type_
#     theta::Context
#     typedArg::Type_
# end


function typer(t::TypeCheckable)
    typer(t.gamma, t.expr, t.typ)
end
function typer(t::TypeSynthable)
    typer(t.gamma, t.expr)
end
function typer(t::TypeAppSynthable)
    typer(t.gamma, t.typ, t.expr)
end

function typer(gamma::Context, expr::EUnit, typ::TUnit)::TypecheckRes
    gamma
end

# First Secret Feature: if lgamma is present, Clip Away context if not Error!!
function typer(tcheckRes::Context, lgamma::Index)::TypecheckRes  # FROM: TypeCheckedToClip
    tcheckRes[1:lgamma]
end


# Second Secret Feature: if typ is present, Decorate context if not Error!!
# Also note how decorator is passed FIRST to distinguish from something you typecheck
# this Secret Feature turns a checked type into a "synthed" one.
# Yes, in real use type always == tcable.typ. I don't care now.
function typer(type::Type_, tcheckRes::Context)::TypesynthRes  # TypeCheckedToMakeSynth
    (type, tcheckRes) 
end


#Third Secret Feature: Apply a Subtyping check to the result of a typeSynth.
# this Secret Feature turns a synthed type into a checked one, if subtypes.
function typer(type::Type_, tsynthResC::Context, tsynthResT::Type_)::TypecheckRes  # TypeSynthedToMakeCheck
    (a, theta) = tsynthResT, tsynthResC
    # subtype(theta, apply(theta, a), apply(theta, typ)) # <------------ THING
    a2, typ2 = apply(theta, a), apply(theta, type)
    # println("after applying $(theta) to $(a) you get: $(a2)")
    # println("after applying $(theta) to $(typ) you get: $(typ2)")
    theta2 = subtype(theta, a2, typ2)
    if theta2 === nothing
        Error("Doesn't typer: $(expr |> pr) is of type $(a2 |> pr) not $(typ2 |> pr) in $(gamma)")
    elseif theta2 isa Error
        Error("Doesn't typer with message: $(theta2)")
    else
        theta2
    end
end


# Fourth Secret Feature: takes a context TO CHECK IN ABS MODE and returns THE CORRESPONDING TFORALL(TFUN).
function typer(tcheckRes::Context, f::ReturnTFunFlag)::TypesynthRes  # TypeCheckedToFunc
    res = tcheckRes
    # res is the TYPECHECKED CONTEXT

    # SIMPLER/ ORIGINAL
    #return (typeof(res) === Error) ? res : (TFun(TProd(texists), beta), res)
    
    # FULL Damas-Milner
    # -- ->I=> Full Damas-Milner type inference
    # are we just assuming it's never an error?
    @assert (! (res isa Error)) res

    lgamma = f.lgamma
    lexpr = f.lexpr
    # IDEA: first 1. you APPPLY all (TExists pointing to) CExistsSolved's directly into return type, second 2. you Turn all REMAINING (TExists pointing to) CExist's into TLoc's !!!

    #1.
    # idea: rn left-to-right dependencies are BROKEN, but EVEN IN THE WORST CASE, i'm NEVER doing the thing of 
    # CHANGING WHAT COMES BEFORE...
    # SO, lgamma is a GOOD INFORMATION about where to split!!!
    texists = [TExists(i + lgamma) for i in 1:lexpr] # pointing to alphas IN delta2 
    beta = TExists(lexpr + lgamma + 1)
    #^ yes right, the equivalent ones above are superfluous // OK no problem at all w/ texists, but beta ????
    tau = apply(res, TFun(TProd(texists), beta), lgamma+1)
    
    (delta, delta2) = res[1:lgamma], res[lgamma+1:end]
    #2.
    evars = [i + lgamma for (i, c) in enumerate(delta2) if c isa CExists]
    for (i_newloc, i_exists) in enumerate(evars)
        tau = substEx(TLoc(i_newloc), i_exists, tau)
    end
    return (TForall(tau), delta)# or res? Don't think gamma...
end


# Base cases: # Are not a problem are they?

function typer(gamma::Context, expr::EGlob)::TypesynthRes 
    (expr.type, gamma)
end

function typer(gamma::Context, expr::ELoc)::TypesynthRes 
    if expr.n > length(gamma)
        throw(DomainError("Undefined local var $(expr.n), n args given = $(length(gamma))"))
    elseif !(gamma[expr.n] isa CVar)
        Error("typer: ELoc not pointing to CVar: var $(expr), in $(gamma)")
    else
        (gamma[expr.n].type, gamma)
    end
end

function typer(gamma::Context, expr::EUnit)::TypesynthRes 
    (TUnit(), gamma)
end

function typer(gamma::Context, typ, expr::Expr)::TypesynthRes
    Error("typer: don't know what to do with: $(gamma), $(typ), $(expr)")
end



###########################################
function typer(lgamma::Index, expr::EProd)::TypesynthRes 
    TypeSynthableToMakeProd(Context([]), 1, Array{Union{TypeSynthable, Type_}}([TypeSynthable(Context([]), d) for d in expr.data]))
end
function typer()::TypesynthRes   # TypeSynthedToMakeProd
    (TProd(sf5.tsynthResTs), sf5.tsynthResC)
end

###########################################
##################################################################
function typer(lgamma::Index, expr::EApp)::TypesynthRes
    TypeSynthableToMakeApp(TypeSynthable(gamma, expr.func), expr.arg)
end
function typer(theta::Context, typedFunc::Type_, typedArg::Type_)::TypesynthRes
    theta
end

##################################################################




# typecheck forall
function typer(lgamma::Index, expr, typ::TForall)::Typable
    ltyp = typ.body |> arity # we DON'T want this to exist :(
    tcable = TypeCheckable(
        [CForall() for i in 1:ltyp], 
        expr,
        subst(Array{Type_}([TLoc(i + lgamma) for i in 1:ltyp]), typ.body)
    )
    # # # ress = typer(TypeCheckableToClip(tcable, lgamma))#first secret feat
    TypeCheckableToClip(tcable, lgamma)
end

function typer(lgamma::Index, expr::EAbs, typ::TFun)::Typable
    lexpr = expr.body |> arity # we DON'T want this to exist
    if lexpr > length(typ.inputs.data) return Error("$(expr |> pr) has too many vars to be of type $(typ |> pr) (the first has $(lexpr) vars, the second $(length(typ.inputs.data)))") end
    tcable = TypeCheckable(
        [CVar(t) for t in typ.inputs.data], 
        subst(Array{Expr}([ELoc(i + lgamma) for i in 1:lexpr]), expr.body),
        typ.t2)
    # # # ress = typer(TypeCheckableToClip(tcable, lgamma)) #first secret feat
    TypeCheckableToClip(tcable, lgamma)
end
# IMPORTANT NOTE: it DOES NOT return the ASSUMPTION WITHIN THE body    

function typer(lgamma::Index, expr::EAnno)::Typable 
    tcable = TypeCheckable(
        Context([]), expr.expr, expr.type)
    # # # ress = typer(TypeCheckableToMakeSynth(expr.type, tcable)) # this Second Secret Feature turns a checked type into a "synthed" one
    TypeCheckableToMakeSynth(expr.type, tcable)
end

function typer(lgamma::Index, expr, typ::Type_)::Typable # check
    # this is good
    tsable = TypeSynthable(Context([]), expr)
    # # # ress = typer(TypeSynthableToMakeCheck(typ, tsable))
    TypeSynthableToMakeCheck(typ, tsable)
end


# (typeof(res) !== Error) ? res[1:sf1.lgamma] : res


# typersecond's CONSUME stack elements, YES. But where do the result go ???
# idea: the result is NOT the prev element in the stack (duh, y would it), instead, new meaning is produced, IN PARTICULAR (but not only), via the MEANING CARRYING TOOL, Context.
# -- | Type synthesising:
# --   typer Γ e = (A, Δ) <=> Γ |- e => A -| Δ

# typer(Context([CVar(TGlob("G"))]), EAnno(EGlobAuto("g"), TExists(1))) # SHOULD raise error
# ^ note that it WORKS, it just returns TExists(1) again

function typer(lgamma::Index, expr::EAbs)::Typable 
    lexpr = expr.body |> arity
    alphas = [CExists() for i in 1:lexpr] 
    x2s = [CVar(TExists(lgamma + i)) for i in 1:lexpr] # x2:alpha
    texists = [TExists(lgamma + i) for i in 1:lexpr] # pointing to alphas
    # positions where x2's end up: lgamma + lexpr + 1 + 1 tolgamma + lexpr + 1 + lexpr
    newlocs = [ELoc(lgamma + lexpr + 1 + i) for i in 1:lexpr] 
    beta = TExists(lgamma + lexpr + 1)

    delta = vcat(gamma, alphas, [CExists()], x2s) # alphaS, beta, vars
    a2 = subst(Array{Expr}(newlocs), expr.body) # var of type alpha   
    # but isn't just alpha enough????????? -> I'm going with NO, now!! (because you would lose EQUALITY, i dunno if it's a thing)
    tcable = TypeCheckable(delta, a2, beta)
    # # # ress = typer(TypeCheckableToFunc(tcable, ReturnTFunFlag(lexpr, lgamma)))
    TypeCheckableToFunc(tcable, ReturnTFunFlag(lexpr, lgamma))
end

# -- | Type application synthesising
# --   typer Γ A e = (C, Δ) <=> Γ |- A . e =>> C -| Δ

function typer(lgamma::Index, typ::TForall, expr::Expr)::Typable
    ltyp = typ.body |> arity # we DON'T want this to exist :(
    tcable = TypeAppSynthable(
        [CExists() for i in 1:ltyp], 
        subst(Array{Type_}([TExists(i + lgamma) for i in 1:ltyp]), typ.body),
        expr,
    )
    # # # ress = typer(tcable)
    tcable
end

function typer(lgamma::Index, typ::TExists, expr::Expr)::Typable
    println("yep.. Definitely happing")
    #                   alpha2, alpha1
    tcable = TypeCheckable(
        [CExists(), CExists(), CExistsSolved(TFun(TExists(lgamma + 2), TExists(lgamma + 1)))],
        expr, TExists(lgamma + 2))
    # # # ress = typer(TypeCheckableToMakeSynth(TExists(lgamma + 1), tcable)) # This is the Second Secret Feature
    TypeCheckableToMakeSynth(TExists(lgamma + 1), tcable)
end

function typer(lgamma::Index, typ::TFun, expr::Expr)::Typable
    tcable = TypeCheckable(Context([]), expr, typ.inputs)
    # # # ress = typer(TypeCheckableToMakeSynth(typ.t2, tcable)) # This is the Second Secret Feature
    TypeCheckableToMakeSynth(typ.t2, tcable)
end



gstack = []











@assert SType |> pr == "([(X->(A->B)) x (X->A) x X]->B)"
@assert STypeP |> pr == "∀(([(T3->(T2->T1)) x (T3->T2) x T3]->T1))"
@assert monotype(TProd([TLoc(1), TExists(2), TFunAuto(TGlob("F"), TExists(3))])) == true
@assert monotype(TProd([TLoc(1), TExists(2), TFunAuto(TGlob("F"), TForall(TLoc(1)))])) == false
@assert subtype(Context([]), TGlob("G"), TGlob("G")) == Context([])
@assert subtype(Context([]), TLoc(3), TLoc(3)) == Context([])
@assert subtype(Context([CExistsSolved(TGlob("G"))]), TGlob("G"), TExists(1)) == Context([CExistsSolved(TGlob("G"))])
@assert subtype(Context([CExistsSolved(TGlob("G"))]), TGlob("F"), TExists(1)) == "subtype, isn't subtypable: TGlob(\"F\"), TGlob(\"G\")"
@assert subtype(Context([CExistsSolved(TGlob("G"))]), TExists(1), TGlob("G")) == Context([CExistsSolved(TGlob("G"))])
@assert subtype(Context([]), TForall(TLoc(1)), TGlob("G")) == Context([])
@assert subtype(Context([]), TForall(TLoc(1)), TFunAuto(TGlob("A"), TGlob("B"))) == Context([])
@assert subtype(Context([]), TForall(TGlob("G")), TGlob("G")) == Context([])
@assert subtype(Context([]), TForall(TGlob("F")), TGlob("G")) == "subtype, isn't subtypable: TGlob(\"F\"), TGlob(\"G\")"
@assert subtype(Context([]), TForall(TFunAuto(TLoc(1), TLoc(2))), TFunAuto(TGlob("A"), TGlob("B"))) == Context([])
@assert subtype(Context([CExists()]), TForall(TExists(1)), TGlob("A")) == Context([CExistsSolved(TGlob("A"))])
@assert subtype(Context([CExists()]), TForall(TFunAuto(TLoc(1), TExists(1))), TFunAuto(TGlob("A"), TGlob("B"))) == Context([CExistsSolved(TGlob("B"))])
@assert typerExecutor(Context([CForall()]), EUnit(), TUnit()) == Context([CForall()])
@assert typerExecutor(Context([]), EUnit(), TForall(TForall(TUnit()))) == Context([])
@assert typerExecutor(Context([]), EAbs(EUnit()), TFunAuto(TForall(TUnit()), TUnit())) == Context([])
@assert typerExecutor(Context([]), EGlobAuto("g"), TGlob("F")) == "Doesn't typer with message: subtype, isn't subtypable: TGlob(\"G\"), TGlob(\"F\")"
@assert subst(Array{Expr}([ELoc(4)]), EAbs(ELoc(1)).body) == ELoc(4)
@assert typerExecutor(Context([CVar(TGlob("F"))]), ELoc(1), TGlob("F")) == Context([CVar(TGlob("F"))])
@assert typerExecutor(Context([CExistsSolved(TGlob("G"))]), EGlobAuto("g"), TExists(1)) == Context([CExistsSolved(TGlob("G"))])
@assert typerExecutor(Context([CExistsSolved(TGlob("G"))]), EGlobAuto("f"), TExists(1)) == "Doesn't typer with message: subtype, isn't subtypable: TGlob(\"F\"), TGlob(\"G\")"
@assert typerExecutor(Context([CExists()]), EGlobAuto("g"), TExists(1)) == Context([CExistsSolved(TGlob("G"))])
@assert typerExecutor(Context([CExists(), CVar(TLoc(1))]), ELoc(2), TExists(1)) == Context([CExistsSolved(TLoc(1)), CVar(TLoc(1))])
@assert typerExecutor(Context([CExistsSolved(TGlob("F")), CVar(TGlob("F"))]), EAnno(ELoc(2), TGlob("F")), TExists(1)) == Context([CExistsSolved(TGlob("F")), CVar(TGlob("F"))])
@assert typerExecutor(Context([CExistsSolved(TGlob("F")), CVar(TExists(1))]), EAnno(ELoc(2), TGlob("F")), TExists(1)) == Context([CExistsSolved(TGlob("F")), CVar(TExists(1))])
@assert typerExecutor(Context([CExists(), CVar(TExists(1))]), EAnno(ELoc(2), TGlob("F")), TExists(1)) == Context([CExistsSolved(TGlob("F")), CVar(TExists(1))])
@assert typerExecutor(Context([CExists(), CVar(TExists(1))]), EAnno(ELoc(2), TExists(1)), TGlob("F")) == Context([CExistsSolved(TGlob("F")), CVar(TExists(1))])
@assert typerExecutor(Context([CExists(), CVar(TLoc(1))]), EAnno(ELoc(2), TLoc(1)), TExists(1)) == Context([CExistsSolved(TLoc(1)), CVar(TLoc(1))])
@assert typerExecutor(Context([CExists(), CVar(TExists(1))]), EProd([EAnno(ELoc(2), TGlob("G")), EAnno(ELoc(2), TExists(1))]), TProd([TExists(1), TGlob("G")])) == Context([CExistsSolved(TGlob("G")), CVar(TExists(1))])

@assert typerExecutor(Context([CVar(TGlob("K"))]), EAnno(EGlobAuto("g"), TGlob("G"))) == (TGlob("G"), ContextElem[CVar(TGlob("K"))])
@assert typerExecutor(Context([CVar(TGlob("K"))]), EAnno(EGlobAuto("f"), TGlob("G"))) == "Doesn't typer with message: subtype, isn't subtypable: TGlob(\"F\"), TGlob(\"G\")" # shouldn't typerExecutor
@assert typerExecutor(Context([CExistsSolved(TGlob("G"))]), EAnno(EGlobAuto("g"), TExists(1))) == (TExists(1), ContextElem[CExistsSolved(TGlob("G"))])
@assert typerExecutor(Context([CVar(TGlob("K"))]), EAbs(EAnno(ELoc(1), TGlob("A")))) == (TForall(TFun(TProd(Type_[TGlob("A")]), TGlob("A"))), ContextElem[CVar(TGlob("K"))])
@assert typerExecutor(Context([]), EAppAuto(EAbs(EProd([ELoc(1), EGlobAuto("g")])), EGlobAuto("f"))) |> (x->apply(x[2], x[1])) == TProd([TGlob("F"), TGlob("G")])
@assert typerExecutor(Context([]), EAnno(EAbs(EProd([ELoc(1), EGlobAuto("g")])), TForall(TFunAuto(TLoc(1), TProd([TLoc(1), TGlob("G")]))))) == (TForall(TFun(TProd([TLoc(1)]), TProd([TLoc(1), TGlob("G")]))), ContextElem[])
@assert typerExecutor(Context([]), EAppAuto(EAbs(EProd([ELoc(1), EGlobAuto("g")])), EGlobAuto("f"))) |> (x->apply(x[2], x[1])) == TProd([TGlob("F"), TGlob("G")])
@assert typerExecutor(Context([CExists(), CVar(TExists(1))]), EAnno(ELoc(2), TLoc(1)), TExists(1)) == Context([CExistsSolved(TLoc(1)), CVar(TExists(1))])

gamma, expr = Context([CVar(TGlob("K"))]), EAbs(ELoc(1))
r1 = typer(gamma, expr) #:: TypeCheckableToFunc
r2 = typer(r1.tcable) # :: TypeSynthableToMakeCheck
r3 = typer(r2.tsable) # :: TypesynthRes
# r4 = typer(r3) # :: TypesynthRes
r3 isa Typed

table_2_ted(t::TypeSynthableToMakeCheck, res::TypesynthRes) = ((type, ctx) = res; (t.type, ctx, type))
table_2_ted(t::TypeCheckableToClip, res::TypecheckRes) = (res, t.lgamma)
table_2_ted(t::TypeCheckableToFunc, res::TypecheckRes) = (res, t.f)
table_2_ted(t::TypeCheckableToMakeSynth, res::TypecheckRes) = (t.type, res)
table_2_ted(t::TypeCheckable, res::TypecheckRes) = res
table_2_ted(t::TypeSynthable, res::TypesynthRes) = res
function table_2_ted(t::TypeSynthableToMakeProd, res::TypesynthRes) 
    (type, ctx) = res
    t.c=ctx
    t.types[t.i] = type
    t.i = t.i+1
    (t.i > t.types |> length) ? (t.c, Array{Type_}(t.types)) : t
end
function table_2_ted(t::TypeSynthableToMakeApp, res::Union{TypesynthRes, TypecheckRes}) 
    if (t.argToBecomeTypeCheckable isa TypeCheckable) & (res isa TypecheckRes)
        TypeSynthedToMakeApp()#smthg, #smthg)
    elseif (t.argToBecomeTypeCheckable isa Expr) & (res isa TypesynthRes)
        TypeSynthableToMakeApp()#smthg, #smthg) # REMBER: check the order!!
    else
        throw(DomainError("Whaat, ")) #probably
end
# tsable = TypeSynthable(gamma, expr.func)
# res = typer(tsable)
# if (typeof(res) === Error) return res end
# (a, theta) = res
# # # # ress = typer(theta, apply(theta, a), expr.arg)
# (theta, apply(theta, a), expr.arg)

# what now ???
get_tcable(t::TypeCheckableToFunc) = t.tcable
get_tcable(t::TypeCheckableToClip) = t.tcable
get_tcable(t::TypeCheckableToMakeSynth) = t.tcable
get_tcable(t::TypeCheckable) = t
get_tcable(t::TypeSynthableToMakeCheck) = t.tsable
get_tcable(t::TypeSynthableToMakeProd) = t.types[i]
get_tcable(t::TypeSynthableToMakeApp) = t.types[i]
get_tcable(t::TypeSynthable) = t

TAble = Union{Typable, Typed, TypecheckRes, TypesynthRes}

function typerExecutor(typable::Typable)
    stack = Array{TAble}([typable])
    # IMPORTANT: PLEASE remember this: KEEP A COMPOUND of all the VARIOUS GAMMA's in Stack and VCAT THEM!
    push!(stack, typer(stack[end]))
    while stack |> length > 1
        # ^ his can be: a Typable, or a Typed, or TypeCheckRes directly (which means can be an error, too.)
        if stack[end] isa Error return stack[end]
        elseif stack[end] isa Typable push!(stack, typer(get_tcable(stack[end])))
        else
            res = typer(pop!(stack))#secret feature!!!
            stack[end] = table_2_ted(stack[end], res) # NOT atcually necessairly to ted every time, and this is RIGHT (cuz DFT, yes :check::check:)
        end
        #println(stack)
    end
    stack[1]
end
typerExecutor(c::Context, e::Expr) = typerExecutor(TypeSynthable(c, e))
typerExecutor(c::Context, e::Expr, t::Type_) = typerExecutor(TypeCheckable(c, e, t))

typerExecutor(gamma, expr)


@assert typer(gamma, expr) == (TForall(TFun(TProd(Type_[TLoc(1)]), TLoc(1))), ContextElem[CVar(TGlob("K"))]) 
c, e = Context([CExists()]), EAnno(EAbs(EProd([ELoc(1), EGlobAuto("g")])), TForall(TFunAuto(TLoc(1), TProd([TLoc(1), TExists(1)]))))
@assert typer(c, e) == (TForall(TFun(TProd(Array{Type_}([TLoc(1)])), TProd(Array{Type_}([TLoc(1), TExists(1)])))), ContextElem[CExistsSolved(TGlob("G"))])




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
EGlob("S", TFunAuto(TGlob("A"), TGlob("B"))) |> pr

# Now polymorphicly:
SType1P = TFunAuto(TLoc(3), TLoc(2))
SType2P = TFunAuto(TLoc(3), TFunAuto(TLoc(2), TLoc(1)))
STypeP = TForall(TFun(TProd([SType2P, SType1P, TLoc(3)]), TLoc(1)))

@assert SType |> pr == "([(X->(A->B)) x (X->A) x X]->B)"
@assert STypeP |> pr == "∀(([(T3->(T2->T1)) x (T3->T2) x T3]->T1))"
typer(Context([]), S, STypeP)
typer(Context([]), S, SType)

S = EAbs(EAppAuto(EAppAuto(EAnno(ELoc(1), TExists(1)), EAnno(ELoc(3), TGlob("X"))), EAnno(EAppAuto(EAnno(ELoc(2),TExists(2)), ELoc(3)), TGlob("A"))))
S |> pr
SType |> pr
cres = typer(Context([CExists(), CExists()]), S, SType) 
println("Type of $(S |> pr) is confirmed $(SType |> pr) in context $(cres .|> pr) !!!")
tres, cres = typer(Context([CExists(), CExists()]), S)
println("Type of $(S |> pr) is generated $(tres |> pr) in context $(cres .|> pr) !!!")



# Other more broken things:
gamma = Context([CVar(TGlob("K")), CExists()])
expr = EAbs(EGlobAuto("g"))
tc = typer(gamma, expr.body, TExists(2))

gamma = Context([CVar(TGlob("K")), CExists(), CExists(), CVar(TExists(2))])
tc = typer(gamma, ELoc(4), TExists(3))
# ^ buuh :(

typer(Context([CVar(TGlob("G"))]), EGlobAuto("f"))
typer(Context([CVar(TGlob("G"))]), ELoc(1))
typer(Context([CExists()]), ELoc(1))
typer(Context([]), EAppAuto(EAbs(EProd([ELoc(1), EGlobAuto("g")])), EGlobAuto("f")))
typer(Context([]), EAppAuto(EAbs(EProd([ELoc(1), EGlobAuto("g")])), EGlobAuto("f")))
typer(Context([]), EProd([EGlobAuto("f"), EGlobAuto("g")]), TForall(TProd([TLoc(1), TLoc(2)])))
c, e, t = Context([CExists(), CVar(TExists(1))]), EProd([ELoc(2)]), TForall(TProd([TLoc(1)]))
typer(c, e, t)
typer(Context([CVar(TGlob("K"))]), EAbs(EGlobAuto("g")))
# gamma = Context([CVar(TGlob("K"))])
# expr = EAbs(ELoc(1))
c = Context([CExists()])
e = EAnno(EAbs(EProd([ELoc(1), EGlobAuto("g")])), TForall(TFunAuto(TLoc(1), TProd([TLoc(1), TExists(1)]))))
EAnno(EAbs(EProd([ELoc(1), EGlobAuto("g")])), TForall(TFunAuto(TLoc(1), TProd([TLoc(1), TExists(1)])))) |>pr