
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

struct TTop <: Type_  end
struct TGlob <: Type_  
    var::Id 
end
struct TLoc <: Type_ 
    var::Index 
end
struct TUnit <: Type_ end
struct TForall <: Type_
    body::Type_ # idea: this CAN contain (type level) local variables
end
struct TFun <: Type_ # 2 or many, but this is the nbvccvnnbvcvcn nvbcnbvc cvnb
    typs_dot_ordered::Array{Type_} # Moslty should compute to PRODS (they are the INTERMEDIATE results)
end
struct TProd <: Type_
    data::Array{Type_}
end
Base.:(==)(a::TProd, b::TProd) = Base.:(==)(a.data, b.data)
Base.:(==)(a::TFun, b::TFun) = a.typs_dot_ordered == b.typs_dot_ordered
Base.:(==)(a::TForall, b::TForall) = Base.:(==)(a.body, b.body)


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


TFunMake(tin, tout) = TFun([tin, tout])
TFunAuto(tin, tout) = TFun([TProd([tin]), tout])


pr(x::TGlob)::String = "$(x.var)"
pr(x::TLoc)::String = "T$(x.var)"
pr(x::TUnit)::String = "UU"
pr(x::TExists)::String = "∃$(x.var)"
pr(x::TForall)::String = "∀($(x.body |> pr))"
pr(x::TProd)::String = "[$(join(x.data .|> pr, " x "))]" 
pr_(x::Type_) = (x isa TProd && length(x.data)==1) ? (x.data[1] |> pr) : (x |> pr)
function pr(x::TFun)::String
    "(" * (x.typs_dot_ordered .|> pr_ |> x->join(x, "->")) * ")"
end


subst(news::Array{Type_}, t::TGlob)::Type_= t 
subst(news::Array{Type_}, t::TLoc)::Type_ = if t.var <= length(news) news[t.var] else throw(DomainError("Undefined local var $(t.var), n args given = $(length(news))" )) end
subst(news::Array{Type_}, t::TUnit)::Type_ = t 
subst(news::Array{Type_}, t::TFun)::Type_ = TFun(t.typs_dot_ordered .|> x->subst(news, x)) 
subst(news::Array{Type_}, t::TForall)::Type_ = t # TForall(subst(news, t.body)) 
subst(news::Array{Type_}, t::TProd)::Type_ = TProd(t.data .|> (x->subst(news, x))) 
subst(news::Array{Type_}, t::TExists)::Type_ = t

reduc(t::TGlob)::Type_ = t
reduc(t::TLoc)::Type_ = t
reduc(t::TUnit)::Type_ = t
reduc(t::TForall)::Type_ = TForall(reduc(t.body))
reduc(t::TFun)::Type_ = (t|>pr|>println; reduc(t.typs_dot_ordered .|> reduc)) # EApp is AN OBJECT THAT REPRESENTS A COMPUTATION (it's only "reduc" here since which one is "typechecked at runtime")
reduc(t::TProd)::Type_ = TProd(t.data .|> reduc)
reduc(t::TExists)::Type_ = t
function reduc(ops::Array{Type_})
    #println("> doing the ", typeof(func),  " ", typeof(arg), " thing")
    if ops[1] isa TForall ops[1] = reduc(Array{Type_}([TProd([]), ops[1]])) end # this is because i still havent decided between prods and 0-arg'd lambda's. 
    #^ this MIGHT VERY WELL FAIL, idk
    while (length(ops) >= 2 && ops[1] isa TProd && ops[2] isa TForall) ops = vcat([subst(ops[1].data, ops[2].body) |> reduc], ops[3:end]) end
    # TODO: make this into a more reasonable stack
    return length(ops) >= 2 ? EApp(ops) : ops[1]
end

# NOT used by the above:
arity(base::Index, t::TGlob)::Index= base 
arity(base::Index, t::TLoc)::Index = max(base, t.var)
arity(base::Index, t::TUnit)::Index = base 
arity(base::Index, t::TFun)::Index = t.typs_dot_ordered .|> (x->arity(base, x)) |> maximum
arity(base::Index, t::TForall)::Index = base # Lam(arity(base, t.body)) 
arity(base::Index, t::TExists)::Index = base
arity(base::Index, t::TProd)::Index = t.data .|> (x->arity(base, x)) |> maximum
arity(t::Type_)::Index = arity(0, t)

EGlob("x", TGlob("A"))
EAnno(ELoc(1), TFunAuto(TGlob("A"), TGlob("B")))
EAnno(ELoc(2), TExists(1))

SType1 = TFunAuto(TGlob("X"), TGlob("A"))
SType2 = TFunAuto(TGlob("X"), TFunAuto(TGlob("A"), TGlob("B")))
SType = TFunAuto(TProd([SType2, SType1, TGlob("X")]), TGlob("B"))


EGlob("S", TFunAuto(TGlob("A"), TGlob("B"))) |> pr
TFunAuto(TGlob("A"), TGlob("B")) |> pr

# Now polymorphicly:
SType1P = TFunAuto(TLoc(3), TLoc(2))
SType2P = TFunAuto(TLoc(3), TFunAuto(TLoc(2), TLoc(1)))
STypeP = TForall(TFunMake(TProd([SType2P, SType1P, TLoc(3)]), TLoc(1)))
STypeP |> pr


########## Context elements:

# i REALLY wish i didn't need these :(
# what these do is: they DEREFERENCE ALL TExists IN THE GAMMA, returning the RESULTING Type_ IF solved, or TExist again if unsolved
# (they are LITERALLY just subst, but for Context/Exists, in other words)
apply(gamma:: Context, typ::TUnit)::Type_ = typ
apply(gamma:: Context, typ::TGlob)::Type_ = typ
apply(gamma:: Context, typ::TLoc)::Type_ = typ
apply(gamma:: Context, typ::TForall)::Type_ = TForall(apply(gamma, typ.body))
apply(gamma:: Context, typ::TProd)::Type_ = TProd(typ.data .|> (x->apply(gamma, x)))
apply(gamma:: Context, typ::TFun)::Type_ = TFun(typ.typs_dot_ordered .|> x->apply(gamma, x))
function apply(gamma:: Context, typ::TExists)::Type_
    # the IDEA would be that this includes findSolved, idk if this turning a O(x) into O(0) means i'm missing something....
    if  typ.var > length(gamma)
        throw(DomainError("Undefined local var $(typ.var), n args given = $(length(gamma))"))
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
apply(gamma:: Context, typ::TFun, lev_to_start_from:: Index)::Type_ = TFun(typ.typs_dot_ordered .|> x->apply(gamma, x, lev_to_start_from))
function apply(gamma:: Context, typ::TExists, lev_to_start_from:: Index)::Type_
    # the IDEA would be that this includes findSolved, idk if this turning a O(x) into O(0) means i'm missing something....
    if typ.var < lev_to_start_from
        typ
    elseif  typ.var > length(gamma)
        throw(DomainError("Undefined local var $(typ.var), n args given = $(length(gamma))"))
    elseif gamma[typ.var] isa CExistsSolved
        apply(gamma, gamma[typ.var].type,lev_to_start_from)
    else
        typ
    end
end
# QUESTION: i COULD rework this^ into a thing that REMOVES the solved ones from the context too, PROPERLY taking care of all he following TExists, BUT:
# Is this what i want? And if yes, always?   # -> What if the solved type is long and complex? We like references, don't we?

# flattenContext(cc::Context, c::CVar) = c
flattenContext(cc::Context, c::CExists) = c
flattenContext(cc::Context, c::CExistsSolved) = CExistsSolved(apply(cc, c.type))
flattenContext(cc::Context)::Context = cc .|> (x->flattenContext(cc,x))
flattenContext(Context([CExists(), CExistsSolved(TExists(3)), CExistsSolved(TExists(4)), CExistsSolved(TGlob("T")), CExistsSolved(TExists(1))]))


apply(Context([CExistsSolved(TGlob("G"))]), TExists(1))

monotype(t::TUnit)::Bool = true # so yes, in its weird way
monotype(t::TGlob)::Bool = true # so yes
monotype(t::TLoc)::Bool = true # so yes
monotype(t::TForall)::Bool = false # so no
monotype(t::TExists)::Bool = true # so yes
monotype(t::TFun)::Bool = t.typs_dot_ordered .|> monotype |> all
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
    # SET POSITION ALPHA TO SOLVED TAU
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
subtype(gamma::Context, alpha::TGlob, alpha2::TGlob)::Union{Context, Error} = ((alpha == alpha2) ? gamma : err(alpha, alpha2))
subtype(gamma::Context, alpha::TUnit, alpha2::TUnit)::Union{Context, Error} = gamma
subtype(gamma::Context, fa::TFun, fb::TFun)::Union{Context, Error} = (c=subtype(gamma, fb.typs_dot_ordered[1], fa.typs_dot_ordered[1]); (c isa Error) ? c : subtype(c, apply(c, fa.typs_dot_ordered[end]), apply(c, fb.typs_dot_ordered[end])))
#^ I DONT KNOW if the above subtyping rule is correct. It might very well not be.
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
    elseif (gamma[alpha2.var] isa CExists) instantiateL(gamma, alpha.var, alpha2) # could SO EASILY be R
    elseif (gamma[alpha.var] isa CExists) 
        println("Yes, it's R'ing :(")
        instantiateR(gamma, alpha, alpha2.var) # could SO EASILY be L
    else err(alpha, alpha2)
    end
end

# ^ MAYBE trying to solve an ALREADY SOLVED Exists is NEVER a thing... ^ ok no but WHY WOULDNT it.....
# to be fair, it DOESN'T happen in typer, as apply() happens FIRST


function subtype(gamma::Context, a, t::TForall) # R: more subtle, contxt is EXTENDED with the loc?
    lgamma, ltyp = length(gamma), t.body |> arity # we DON'T want this to exist :(
    gamma2 = vcat(gamma, [CExists() for i in 1:ltyp]) ##################################### it WAS CForall
    sbody = subst(Array{Type_}([TExists(lgamma + i) for i in 1:ltyp]), t.body) ##################################### it WAS TLoc
    gamma_res = subtype(gamma2, a, sbody)
    # dropMarker(vc, gamma_res)  # i don't know how to drop U_U
    gamma_res
end
function subtype(gamma::Context, a::TForall, t::TForall) # the same PREVIOUS case
    lgamma, ltyp = length(gamma), t.body |> arity # we DON'T want this to exist :(
    gamma2 = vcat(gamma, [CExists() for i in 1:ltyp]) ##################################### it WAS CForall
    sbody = subst(Array{Type_}([TExists(lgamma + i) for i in 1:ltyp]), t.body) ##################################### it WAS TLoc
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
function subtype(gamma::Context, t::TForall, b::TExists) # the TForall case, to disambiguate
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
substEx(new::Type_, var::Index, expr::TFun)::Type_ = TFun(expr.typs_dot_ordered .|> (x->substEx(new, var, x)))
substEx(new::Type_, var::Index, expr::TExists)::Type_ = (expr.var == var ? new : expr)
# substEx(new::Type_, var::Index, expr::TForall)::Type_ = TForall(substEx(new, var, expr.body)) 
# ^it's MORE COMPLICATED than this, due to the fact that, INTO THE SCOPE, Loc's HAVE A MEANING already...



# -- | Type checking:
# --   typer Γ e A = Δ <=> Γ |- e <= A -| Δ



###############################################################################

abstract type Typable end
abstract type Typed end
abstract type T2Container end

struct TypeCheckable <: Typable
    expr::Expr
    typ::Type_
end
struct TypeSynthable <: Typable
    expr::Expr
end
struct TypeAppSynthable <: Typable
    typ::Type_
    expr::Expr
end
struct TypeChecked <: Typed
end
struct TypeSynthed <: Typed
    typ::Type_
end
# struct TypeAppSynthed <: Typed  # i THINK it's just TypeSynthed
#     typ::Type_
#     expr::Expr
# end

struct TypeCheckContainerBase <: T2Container
    t::Union{TypeCheckable, TypeChecked}
end
struct TypeSynthContainerBase <: T2Container
    t::Union{TypeSynthable, TypeSynthed}
end
struct TypeAppSynthContainerBase <: T2Container
    t::Union{TypeAppSynthable, TypeSynthed}
end
struct TypeCheckToClip <: T2Container  # First secret Feature
    t::Union{TypeCheckable, TypeChecked}
    lgamma::Index
end
struct TypeCheckToMakeSynth <: T2Container  # Second secret Feature
    type::Type_
    t::Union{TypeCheckable, TypeChecked}
end
struct TypeCheckToMakeSynthANDApply <: T2Container  # Second secret Feature
    type::Type_
    t::Union{TypeCheckable, TypeChecked}
end
struct TypeSynthToMakeCheck <: T2Container  # Third secret Feature
    type::Type_
    t::Union{TypeSynthable, TypeSynthed}
end


struct ReturnTFunFlag
    lexprs::Array{Index}
    lgamma::Index
end
struct TypeCheckToFunc <: T2Container  # Fourth secret Feature
    t::Union{TypeCheckable, TypeChecked}
    f::ReturnTFunFlag
end
mutable struct TypeSynthToMakeProd <: T2Container  # Fifth secret Feature
    i::Int # where you at (what's the NEXT TO DO, so starts at 1)
    types::Array{Union{TypeSynthable, Type_}}
end
mutable struct TypeSynthToMakeApp <: T2Container  # Sixth secret Feature
    types::Array{Union{Expr, TypeSynthed}}
end
struct TypeSynthToJustDereference <: T2Container
    var::Index
    goBack::Bool
end

struct T2ContainerWC
    gamma::Context
    t::T2Container

end
TypecheckRes = Union{Error, T2ContainerWC}
TypesynthRes = Union{Error, T2ContainerWC}

##############################################


function typer(gamma::Context, expr::EUnit, typ::TUnit)::TypecheckRes
    T2ContainerWC(gamma, TypeChecked(), )
end

typer2(gamma::Context, t::TypeCheckContainerBase) = gamma  
# ^ assumed to be ted'ed  # Do nothing
typer2(gamma::Context, t::TypeSynthContainerBase) = typer2(gamma, t.t.typ)  
# ^ assumed to be ted'ed  # do nothing

# First Secret Feature: if lgamma is present, Clip Away context if not Error!!
function typer2(gamma::Context, t::TypeCheckToClip)::TypecheckRes  # FROM: TypeCheckedToClip
    # ^ assumed to be ted'ed #OK  # First Secret Feature
    T2ContainerWC(gamma[1:t.lgamma], TypeCheckContainerBase(TypeChecked()), )
end


# Second Secret Feature: if typ is present, Decorate context if not Error!!
# this Secret Feature turns a checked type into a "synthed" one.
function typer2(gamma::Context, t::TypeCheckToMakeSynth)::TypesynthRes  # TypeCheckedToMakeSynth
    # ^ assumed to be ted'ed #OK  # Second Secret Feature
    T2ContainerWC(gamma, TypeSynthContainerBase(TypeSynthed(t.type)), ) 
end

# EIGHT Secret Feature: if typ is present, Decorate context if not Error!! AND APPLY <<<<<<<<<<<<<
# This is to solve out the context from synthApp's .......  >>> PROBLEMS THAT I CURRENTLY SEE: What if by BRUTALLY APPLYING i am LOSING some info of the kind, " a tforall shoul be instantiated ONCE and mantain that equality(refrerence) contraint" ?? > Very vague i know
# this Secret Feature turns a checked type into a "synthed" one.
function typer2(gamma::Context, t::TypeCheckToMakeSynthANDApply)::TypesynthRes  # TypeCheckedToMakeSynth
    # ^ assumed to be ted'ed #OK  # Second Secret Feature
    gamma = flattenContext(gamma)
    T2ContainerWC(gamma, TypeSynthContainerBase(TypeSynthed(apply(gamma, t.type))), ) 
end

#Third Secret Feature: Apply a Subtyping check to the result of a typeSynth.
# this Secret Feature turns a synthed type into a checked one, if subtypes.
function typer2(gamma::Context, t::TypeSynthToMakeCheck)::TypecheckRes  # TypeSynthedToMakeCheck
    # ^ assumed to be ted'ed  # Third Secret Feature
    (a, theta) = t.t.typ, gamma
    # subtype(theta, apply(theta, a), apply(theta, typ)) # <------------ THING
    a2, typ2 = apply(theta, a), apply(theta, t.type)
    # println("after applying $(theta) to $(a) you get: $(a2)")
    # println("after applying $(theta) to $(typ) you get: $(typ2)")
    theta2 = subtype(theta, a2, typ2)
    if theta2 === nothing
        Error("Doesn't typer: $(expr |> pr) is of type $(a2 |> pr) not $(typ2 |> pr) in $(gamma)")
    elseif theta2 isa Error
        Error("Doesn't typer with message: $(theta2)")
    else
        T2ContainerWC(theta2, TypeCheckContainerBase(TypeChecked()), )
    end
end


# Fourth Secret Feature: takes a context TO CHECK IN ABS MODE and returns THE CORRESPONDING TFORALL(TFUN).
function typer2(gamma::Context, t::TypeCheckToFunc)::TypesynthRes  # TypeCheckedToFunc
    # ^ assumed to be ted'ed  # Fourth secret Feature
    res = gamma
    # res is the TYPECHECKED CONTEXT

    # SIMPLER/ ORIGINAL
    #return (typeof(res) === Error) ? res : (TFun(TProd(texists), beta), res)
    
    # FULL Damas-Milner
    # -- ->I=> Full Damas-Milner type inference
    # are we just assuming it's never an error?
    @assert (! (res isa Error)) res

    lgamma = t.f.lgamma
    lexprs = t.f.lexprs
    # IDEA: first 1. you APPPLY all (TExists pointing to) CExistsSolved's directly into return type, second 2. you Turn all REMAINING (TExists pointing to) CExist's into TLoc's !!!

    #1.
    beta = TExists((lexprs|>sum) + lgamma + 1) # this SHOULD BE EQUIVALENT to what you get from >>> t.t <<< !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
    # idea: rn left-to-right dependencies are BROKEN, but EVEN IN THE WORST CASE, i'm NEVER doing the thing of 
    # CHANGING WHAT COMES BEFORE...
    # SO, lgamma is a GOOD INFORMATION about where to split!!!
    (delta, delta2) = res[1:lgamma], res[lgamma+1:end]
    indices = lexprs |> (x->vcat([1], x)) |> cumsum
    newLocs = [indices[l]:(indices[l+1]-1) for l in 1:length(indices)-1]
    args = [TProd([TExists(i + lgamma) for i in l]) for l in newLocs] # pointing to alphas IN delta2 
    tau = apply(res, TFun(vcat(args, [beta])), lgamma+1)
    
    #2.
    evars = [i + lgamma for (i, c) in enumerate(delta2) if c isa CExists]
    for (i_newloc, i_exists) in enumerate(evars)
        tau = substEx(TLoc(i_newloc), i_exists, tau)
    end
    return T2ContainerWC(delta, TypeSynthContainerBase(TypeSynthed(TForall(tau))) )# or res? Don't think gamma...
end

function typer2(c::Context, t::TypeSynthed)::TypesynthRes T2ContainerWC(c, TypeSynthContainerBase(TypeSynthed(t))) end # do literally nothing howbouthat
typer2(c::Context, t::Type_, )::TypesynthRes = T2ContainerWC(c, TypeSynthContainerBase(TypeSynthed(t))) # do literally nothing howbouthat
typer2(c::Context)::TypecheckRes = T2ContainerWC(c, TypeCheckContainerBase(TypeChecked()))  # do literally nothing howbouthat


###########################################
function typer(lgamma::Index, expr::EProd)::T2ContainerWC 
    arr = Array{Union{TypeSynthable, Type_}}([TypeSynthable(d) for d in expr.data])
    T2ContainerWC(Context([]), TypeSynthToMakeProd(1, arr))# Do you need a context here ???????????????????????????????????????????????
end
# This is kind of a secret feature too:
function typer2(gamma::Context, t::TypeSynthToMakeProd)::TypesynthRes   # TypeSynthedToMakeProd
    # ^ assumed to be ted'ed  # <----- it will AUTOMATICALLY BREAK if not  # Fifth Secret Feature
    T2ContainerWC(gamma , TypeSynthContainerBase(TypeSynthed(TProd(Array{Type_}(t.types)))) )
end

###########################################
##################################################################
function typer(lgamma::Index, expr::EApp)::T2ContainerWC
    T2ContainerWC(Context([]), TypeSynthToMakeApp(expr.ops_dot_ordered)) # Do you need a context here ???????????????????????????????????????????????
end
# This is kind of a secret feature too:
function typer2(gamma::Context, t::TypeSynthToMakeApp)::TypesynthRes
    # ^ assumed to be ted'ed  # Sixth Secret Feature
    @assert t.types[1] isa TypeSynthed
    T2ContainerWC(gamma, TypeSynthContainerBase(t.types[1]))
end
typer2(gamma::Context, t::TypeAppSynthContainerBase) = (gamma=flattenContext(gamma); typer2(gamma, apply(gamma, t.t.typ)))
# ^ assumed to be ted'ed  # do THIS VERY SPECIFIC THING !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!

##################################################################

# THIS IS ALSO A SECRET FEATURE- the SEVENTH (don't tell anybody):
function typer2(gamma::Context, t::TypeSynthToJustDereference)::TypesynthRes 
    # ^ assumed to be ted'ed  # Seventh seventh Secret Feature
    if t.var > length(gamma)
        throw(DomainError("Undefined local var $(t.var), n args given = $(length(gamma))"))
    elseif gamma[t.var] isa CExistsSolved
        T2ContainerWC(gamma, TypeSynthContainerBase(TypeSynthed(gamma[t.var].type)), )
    else
        T2ContainerWC(gamma, TypeSynthContainerBase(TypeSynthed(TExists(t.var))), )
    end    
end  


# Base cases: # Are not a problem are they?---   # HA.



typer(lgamma::Index, t::TypeCheckToFunc) = typer(lgamma, t.t.expr, t.t.typ)
typer(lgamma::Index, t::TypeCheckToClip) = typer(lgamma, t.t.expr, t.t.typ)
typer(lgamma::Index, t::TypeCheckToMakeSynth) = typer(lgamma, t.t.expr, t.t.typ)
typer(lgamma::Index, t::TypeCheckToMakeSynthANDApply) = typer(lgamma, t.t.expr, t.t.typ)
typer(lgamma::Index, t::TypeCheckContainerBase) = typer(lgamma, t.t.expr, t.t.typ)
typer(lgamma::Index, t::TypeSynthToMakeCheck) = typer(lgamma, t.t.expr)
typer(lgamma::Index, t::TypeSynthToJustDereference) = nothing
typer(lgamma::Index, t::TypeSynthToMakeProd) = typer(lgamma, t.types[t.i].expr)
typer(lgamma::Index, t::TypeSynthContainerBase) = typer(lgamma, t.t.expr)
typer(lgamma::Index, t::TypeAppSynthContainerBase) = typer(lgamma, t.t.typ, t.t.expr)
function typer(lgamma::Index, t::TypeSynthToMakeApp) 
    @assert t.types|>length == 2 "TEMPORARY assert because figuring this out is hard"
    i=findlast(t.types .|> x->x isa Expr)
    if i==t.types|>length typer(lgamma, t.types[i]) # type SYNTHing FUNC
    else typer(lgamma, t.types[end].typ, t.types[i]) # type APPLY-SYNTHing ARG (and getting result)
    # I HOPE it can be asserted that goes inth apply-synth...
    end
end

function typer(lgamma::Index, expr::EGlob)::TypesynthRes 
    T2ContainerWC(Context([]), TypeSynthContainerBase(TypeSynthed(expr.type)))
end    

function typer(lgamma::Index, expr::ELoc)::T2ContainerWC
    T2ContainerWC(Context([]), TypeSynthToJustDereference(expr.n, false))
end
  
function typer(lgamma::Index, expr::EUnit)::TypesynthRes 
    T2ContainerWC(Context([]), TypeSynthContainerBase(TypeSynthed(TUnit())), )
end    

function typer(lgamma::Index, typ, expr::Expr)::TypesynthRes
    Error("typer: don't know what to do with: $(gamma), $(typ), $(expr)")
end    

# typecheck forall
function typer(lgamma::Index, expr, typ::TForall)::T2ContainerWC
    ltyp = typ.body |> arity # we DON'T want this to exist :(
    tcable = T2ContainerWC(Context([CExists() for i in 1:ltyp]), 
        TypeCheckToClip(
            TypeCheckable(expr,
                subst(Array{Type_}([TExists(i + lgamma) for i in 1:ltyp]), typ.body)),
            lgamma
    ))
    tcable
end

function typer(lgamma::Index, expr::EAbs, typ::TFun)::Union{T2ContainerWC, Error}
    lexpr = expr.body |> arity # we DON'T want this to exist
    if typ.typs_dot_ordered |> length > 2 return Error("An EAbs can only be a TFun with a single input and output, not a TFun intended as a computation and definitely not $(typ)") end
    inputstypes, restype = typ.typs_dot_ordered[1], typ.typs_dot_ordered[2]
    if lexpr > length(inputstypes.data) return Error("$(expr |> pr) has too many vars to be of type $(typ |> pr) (the first has $(lexpr) vars, the second $(length(inputstypes.data)))") end
    tcable = T2ContainerWC(Context([CExistsSolved(t) for t in inputstypes.data]),
        TypeCheckToClip(
            TypeCheckable(subst(Array{Expr}([ELoc(i + lgamma) for i in 1:lexpr]), expr.body),
            restype),
            lgamma))
    tcable
end
# IMPORTANT NOTE: it DOES NOT return the ASSUMPTION WITHIN THE body    

function typer(lgamma::Index, expr::EAnno)::T2ContainerWC 
    tcable = T2ContainerWC(Context([]), 
        TypeCheckToMakeSynth(
            expr.type, TypeCheckable(expr.expr, expr.type)
    ))
    tcable
end

function typer(lgamma::Index, expr, typ::Type_)::T2ContainerWC # check
    # this is good
    tsable = T2ContainerWC(Context([]), TypeSynthToMakeCheck(typ, TypeSynthable(expr)))
    tsable
end


# (typeof(res) !== Error) ? res[1:sf1.lgamma] : res


# typersecond's CONSUME stack elements, YES. But where do the result go ???
# idea: the result is NOT the prev element in the stack (duh, y would it), instead, new meaning is produced, IN PARTICULAR (but not only), via the MEANING CARRYING TOOL, Context.
# -- | Type synthesising:
# --   typer Γ e = (A, Δ) <=> Γ |- e => A -| Δ

# typer(Context([CVar(TGlob("G"))]), EAnno(EGlobAuto("g"), TExists(1))) # SHOULD raise error
# ^ note that it WORKS, it just returns TExists(1) again

function typer(lgamma::Index, expr::EAbs)::T2ContainerWC 
    lexpr = expr.body |> arity
    alphas = [CExists() for i in 1:lexpr] 
    # positions where x2's end up: lgamma + lexpr + 1 + 1 tolgamma + lexpr + 1 + lexpr
    newlocs = [ELoc(lgamma + i) for i in 1:lexpr] 
    beta = TExists(lgamma + lexpr + 1)

    delta = vcat(alphas, [CExists()]) # alphaS, beta, vars
    a2 = subst(Array{Expr}(newlocs), expr.body) # var of type alpha   
    # but isn't just alpha enough????????? -> I'm going with NO, now!! (because you would lose EQUALITY, i dunno if it's a thing)
    T2ContainerWC(delta, TypeCheckToFunc(TypeCheckable(a2, beta), ReturnTFunFlag([lexpr], lgamma)))
end

# -- | Type application synthesising
# --   typer Γ A e = (C, Δ) <=> Γ |- A . e =>> C -| Δ

function typer(lgamma::Index, typ::TForall, expr::Expr)::T2ContainerWC # type is the FUNC and expr the ARG
    ltyp = typ.body |> arity # we DON'T want this to exist :(
    println("yep.. This is the place")
    tcable = T2ContainerWC(Context([CExists() for i in 1:ltyp]),
        TypeAppSynthContainerBase(TypeAppSynthable(
            subst(Array{Type_}([TExists(i + lgamma) for i in 1:ltyp]), typ.body),
            expr,
    )))
    tcable
end

function typer(lgamma::Index, typ::TExists, expr::Expr)::T2ContainerWC # type is the FUNC and expr the ARG
    println("yep.. Definitely happing")
    tcable = T2ContainerWC(
        #           alpha2, alpha1
        Context([CExists(), CExists(), CExistsSolved(TFun([TExists(lgamma + 2), TExists(lgamma + 1)]))]),
        TypeCheckToMakeSynthANDApply(TExists(lgamma + 1), TypeCheckable(expr, TExists(lgamma + 2))))
    tcable
end

function typer(lgamma::Index, typ::TFun, expr::Expr)::T2ContainerWC # type is the FUNC and expr the ARG
    @assert typ.typs_dot_ordered |> length ==2 typ
    tcable = T2ContainerWC(Context([]), TypeCheckToMakeSynth(typ.typs_dot_ordered[2], TypeCheckable(expr, typ.typs_dot_ordered[1])))
    tcable
end


typer(lgamma::Index, c::Nothing) = c ## This is a BASE CASE USED FOR JustDereference



table_2_ted(t::TypeSynthToMakeCheck, res::TypeSynthed)::TypeSynthToMakeCheck = TypeSynthToMakeCheck(t.type, res)  
table_2_ted(t::TypeCheckToClip, res::TypeChecked)::TypeCheckToClip = TypeCheckToClip(res, t.lgamma)
table_2_ted(t::TypeCheckToFunc, res::TypeChecked)::TypeCheckToFunc = TypeCheckToFunc(res, t.f) 
table_2_ted(t::TypeCheckToMakeSynth, res::TypeChecked)::TypeCheckToMakeSynth = TypeCheckToMakeSynth(t.type, res) 
table_2_ted(t::TypeCheckToMakeSynthANDApply, res::TypeChecked)::TypeCheckToMakeSynthANDApply = TypeCheckToMakeSynthANDApply(t.type, res) 
table_2_ted(t::TypeCheckContainerBase, res::TypeChecked)::TypeCheckContainerBase = TypeCheckContainerBase(res) 
table_2_ted(t::TypeSynthContainerBase, res::TypeSynthed)::TypeSynthContainerBase = TypeSynthContainerBase(res) 
table_2_ted(t::TypeAppSynthContainerBase, res::TypeSynthed)::TypeAppSynthContainerBase = TypeAppSynthContainerBase(res) # ?????????????????????????????????????
table_2_ted(t::TypeAppSynthContainerBase, res::TypeSynthed)::TypeAppSynthContainerBase = TypeAppSynthContainerBase(res) # ?????????????????????????????????????
    #@assert (!(res isa Error)) && (length(res[2]) == 0) (res) # god i hope this makes sense...
function table_2_ted(t::TypeSynthToMakeProd, res::TypeSynthed)::TypeSynthToMakeProd 
    t.types[t.i] = res.typ
    t.i = t.i+1
    # (t.i > t.types |> length) ? TypeSynthToMakeProd(t.i, Array{Type_}(t.types)) : t
    t
end
function table_2_ted(t::TypeSynthToMakeApp, res::TypeSynthed)::TypeSynthToMakeApp  # NOT a ted at all, you'll notice
    i = findlast(t.types .|> x->x isa Expr)
    t.types[i] = res
    t
end
# function table_2_ted(t::TypeSynthContainerBase, res::TypeAppSynthable)::TypeAppSynthContainerBase 
#     # This is for the TRICK where the APP routine does NOT return a TypED after typer2. :check:
#     # to be fair this is UGLY, but hey if it works it works
#     println(res)
#     TypeAppSynthContainerBase(res)
# end

# True if "there is still work to do "
is_typable(obj::T2ContainerWC) = is_typable(obj.t)
is_typable(obj::T2Container) = obj.t isa Typable
is_typable(obj::TypeSynthToMakeApp) = obj.types .|> (x->x isa Expr) |> any
is_typable(obj::TypeSynthToMakeProd) = (obj.i <= obj.types |> length)
is_typable(obj::TypeSynthToJustDereference) = obj.goBack === false


makeBigStack(s::Array{T2ContainerWC}) = s .|> (x->x.gamma) |> (x->vcat(x...))
function splitBigStack(s::Array{T2ContainerWC}, bigstack)::Array{T2ContainerWC}
    indices = s .|> (x->x.gamma) .|> length |> (x->vcat([1], x)) |> cumsum
    newgammas = [bigstack[
        min(indices[i], length(bigstack) + 1):min(indices[i+1]-1, length(bigstack))] 
        for i in 1:length(indices)-1]
    @assert (length(newgammas) == length(s)) string(length(newgammas))*" "*string(length(s))
    Array{T2ContainerWC}([T2ContainerWC(newgammas[i], s[i].t) for i in 1:length(newgammas)])
end
# s = [3,2,3,6,7]  #|> cumsum
# bs = [40,40,40,50,50,60,60,60,70,70,70,70,70,70,80,80,80,80,80,80,80,] 

function typerExecutor(c::Context, typable::T2Container)
    stack = Array{T2ContainerWC}([T2ContainerWC(c, TypeCheckContainerBase(TypeChecked())), T2ContainerWC(Context([]), typable)])
    # IMPORTANT: PLEASE remember this: KEEP A COMPOUND of all the VARIOUS GAMMA's in Stack and VCAT THEM!
    push!(stack, typer(stack .|> (x->x.gamma) .|> length |> sum, stack[end].t))
    while stack |> length > 2 || stack[end] |> is_typable
        # ^ his can be: a Typable, or a TypeSynthRes or TypeCheckRes directly (which means can be an error, too.)
        if stack[end] isa Error print("FIRST fail"); return stack[end]
        elseif stack[end] |> is_typable
            youGot = typer(stack .|> (x->x.gamma) .|> length |> sum, stack[end].t)
            if youGot isa Error print("SECOND fail"); return youGot end
            if youGot === nothing # Yes, there's a base case. For dereference. Deal with it. 
                stack[end] = T2ContainerWC(stack[end].gamma, TypeSynthToJustDereference(stack[end].t.var, true)) # TypeSynthedToJustDereference
            else
                push!(stack, youGot)
            end
        else
            biggamma = makeBigStack(stack)
            res = typer2(biggamma, stack[end].t)  # secret feature!!!
            if res isa Error print("THIRD fail"); return res end
            stack = splitBigStack(stack, res.gamma)
            pop!(stack)
            WHAT = table_2_ted(stack[end].t, res.t.t) # NOT atcually necessairly to ted every time, and this is RIGHT (cuz DFT, yes :check::check:)
            stack[end] = T2ContainerWC(stack[end].gamma, WHAT)
        end
        #println(stack)
    end
    if stack[end].t.t isa TypeChecked
        makeBigStack(stack)
    else
        (stack[end].t.t.typ, makeBigStack(stack))
    end
end
typerExecutor(c::Context, e::Expr) = typerExecutor(c, TypeSynthContainerBase(TypeSynthable(e)))
typerExecutor(c::Context, e::Expr, t::Type_) = typerExecutor(c, TypeCheckContainerBase(TypeCheckable(e, t)))




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
@assert subst(Array{Expr}([ELoc(4)]), EAbs(ELoc(1)).body) == ELoc(4)

@assert typerExecutor(Context([CExists()]), EUnit(), TUnit()) == Context([CExists()])
@assert typerExecutor(Context([]), EUnit(), TForall(TForall(TUnit()))) == Context([])
@assert typerExecutor(Context([]), EAbs(EUnit()), TFunAuto(TForall(TUnit()), TUnit())) == Context([])
@assert typerExecutor(Context([]), EGlobAuto("g"), TGlob("F")) == "Doesn't typer with message: subtype, isn't subtypable: TGlob(\"G\"), TGlob(\"F\")"
@assert typerExecutor(Context([CExistsSolved(TGlob("F"))]), ELoc(1), TGlob("F")) == Context([CExistsSolved(TGlob("F"))])
@assert typerExecutor(Context([]), EGlobAuto("f"),  TForall(TLoc(1))) == Context([])
@assert typerExecutor(Context([]), EProd([EGlobAuto("g"), EGlobAuto("f")]),  TForall(TProd([TLoc(1), TGlob("F")]))) == Context([])
@assert typerExecutor(Context([CExistsSolved(TGlob("G"))]), EGlobAuto("g"), TExists(1)) == Context([CExistsSolved(TGlob("G"))])
@assert typerExecutor(Context([CExistsSolved(TGlob("G"))]), EGlobAuto("f"), TExists(1)) == "Doesn't typer with message: subtype, isn't subtypable: TGlob(\"F\"), TGlob(\"G\")"
@assert typerExecutor(Context([CExists()]), EGlobAuto("g"), TExists(1)) == Context([CExistsSolved(TGlob("G"))])
@assert typerExecutor(Context([CExists(), CExistsSolved(TLoc(1))]), ELoc(2), TExists(1)) == Context([CExistsSolved(TLoc(1)), CExistsSolved(TLoc(1))])
@assert typerExecutor(Context([CExistsSolved(TGlob("F")), CExistsSolved(TGlob("F"))]), EAnno(ELoc(2), TGlob("F")), TExists(1)) == Context([CExistsSolved(TGlob("F")), CExistsSolved(TGlob("F"))])
@assert typerExecutor(Context([CExistsSolved(TGlob("F")), CExistsSolved(TExists(1))]), EAnno(ELoc(2), TGlob("F")), TExists(1)) == Context([CExistsSolved(TGlob("F")), CExistsSolved(TExists(1))])
@assert typerExecutor(Context([CExists(), CExistsSolved(TExists(1))]), EAnno(ELoc(2), TGlob("F")), TExists(1)) == Context([CExistsSolved(TGlob("F")), CExistsSolved(TExists(1))])
@assert typerExecutor(Context([CExists(), CExistsSolved(TExists(1))]), EAnno(ELoc(2), TExists(1)), TGlob("F")) == Context([CExistsSolved(TGlob("F")), CExistsSolved(TExists(1))])
@assert typerExecutor(Context([CExists(), CExistsSolved(TLoc(1))]), EAnno(ELoc(2), TLoc(1)), TExists(1)) == Context([CExistsSolved(TLoc(1)), CExistsSolved(TLoc(1))])
@assert typerExecutor(Context([CExists(), CExistsSolved(TExists(1))]), EProd([EAnno(ELoc(2), TGlob("G")), EAnno(ELoc(2), TExists(1))]), TProd([TExists(1), TGlob("G")])) == Context([CExistsSolved(TGlob("G")), CExistsSolved(TExists(1))])
@assert typerExecutor(Context([CExistsSolved(TGlob("K"))]), EAnno(EGlobAuto("g"), TGlob("G"))) == (TGlob("G"), ContextElem[CExistsSolved(TGlob("K"))])
@assert typerExecutor(Context([CExistsSolved(TGlob("K"))]), EAnno(EGlobAuto("f"), TGlob("G"))) == "Doesn't typer with message: subtype, isn't subtypable: TGlob(\"F\"), TGlob(\"G\")" # shouldn't typerExecutor
@assert typerExecutor(Context([CExistsSolved(TGlob("G"))]), EAnno(EGlobAuto("g"), TExists(1))) == (TExists(1), ContextElem[CExistsSolved(TGlob("G"))])
@assert typerExecutor(Context([CExists(), CExistsSolved(TExists(1))]), EAnno(ELoc(2), TLoc(1)), TExists(1)) == Context([CExistsSolved(TLoc(1)), CExistsSolved(TExists(1))])
@assert typerExecutor(Context([CExistsSolved(TGlob("K"))]), EAbs(EAnno(ELoc(1), TGlob("A")))) == (TForall(TFunMake(TProd(Type_[TGlob("A")]), TGlob("A"))), ContextElem[CExistsSolved(TGlob("K"))])
@assert typerExecutor(Context([]), EAnno(EAbs(EProd([ELoc(1), EGlobAuto("g")])), TForall(TFunAuto(TLoc(1), TProd([TLoc(1), TGlob("G")]))))) == (TForall(TFunMake(TProd([TLoc(1)]), TProd([TLoc(1), TGlob("G")]))), ContextElem[])
@assert typerExecutor(Context([CExistsSolved(TGlob("K"))]), EAbs(ELoc(1))) == (TForall(TFunMake(TProd(Type_[TLoc(1)]), TLoc(1))), ContextElem[CExistsSolved(TGlob("K"))])
@assert typerExecutor(Context([]), EAbs(EProd([EAnno(ELoc(1), TGlob("T")), ELoc(1)]))) == (TForall(TFun(Type_[TProd(Type_[TGlob("T")]), TProd(Type_[TGlob("T"), TGlob("T")])])), ContextElem[])
@assert typerExecutor(Context([CExists()]), EAbs(EProd([EAnno(ELoc(1), TExists(1)), ELoc(1)])), TFunAuto(TGlob("A"), TProd([TGlob("A"),TGlob("A")]))) == Context([CExistsSolved(TGlob("A"))])
@assert typerExecutor(Context([]), EAbs(EProd([EAnno(ELoc(1), TGlob("B")), ELoc(1)])), TForall(TFunAuto(TLoc(1), TProd([TLoc(1),TLoc(1)])))) == Context([])
@assert typerExecutor(Context([]), EAbs(EProd([EAnno(ELoc(1), TGlob("B")), ELoc(1)])), TForall(TFunAuto(TLoc(1), TProd([TLoc(2),TLoc(3)])))) == Context([])
typerExecutor(Context([CExists()]), EAbs(EProd([EAnno(ELoc(1), TExists(1)), ELoc(1)])), TForall(TFunAuto(TLoc(1), TProd([TLoc(1),TLoc(1)]))))
@assert typerExecutor(Context([]), EAppAuto(EAbs(EProd([ELoc(1), EGlobAuto("g")])), EGlobAuto("f"))) |> (x->apply(x[2], x[1])) == TProd([TGlob("F"), TGlob("G")])
@assert typerExecutor(Context([CExists()]), EAppAuto(EAbs(EProd([EAnno(ELoc(1), TExists(1)), EGlobAuto("g")])), EGlobAuto("f"))) == (TProd(Type_[TGlob("F"), TGlob("G")]), ContextElem[CExistsSolved(TGlob("F"))])
c, e = Context([CExists()]), EAnno(EAbs(EProd([ELoc(1), EGlobAuto("g")])), TForall(TFunAuto(TLoc(1), TProd([TLoc(1), TExists(1)]))))
@assert typerExecutor(c, e) == (TForall(TFunMake(TProd(Array{Type_}([TLoc(1)])), TProd(Array{Type_}([TLoc(1), TExists(1)])))), ContextElem[CExistsSolved(TGlob("G"))])


typerExecutor(Context([CExists()]), EAnno(EProd([EGlobAuto("f"), EGlobAuto("g")]), TExists(1)))
typerExecutor(Context([CExists()]), EAnno(EProd([ELoc(1), EGlobAuto("g")]), TProd([TGlob("F"), TGlob("G")])))

# BROKEN

typerExecutor(Context([CExists(), CExistsSolved(TExists(1))]), EAnno(EAppAuto(ELoc(2), EGlobAuto("f")), TGlob("G")))# actually breaks
typerExecutor(Context([CExists(), CExistsSolved(TExists(1))]), EAppAuto(ELoc(2), EGlobAuto("f"))) == (TGlob("F"), Context([CExistsSolved(TForall(TFun(TProd([TGlob("F")]), TLoc(1)))), CExistsSolved(TExists(1))]))# "breaks" 







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
typerExecutor(Context([]), S, STypeP)
typerExecutor(Context([]), S, SType)

S = EAbs(EAppAuto(EAppAuto(EAnno(ELoc(1), TExists(1)), EAnno(ELoc(3), TGlob("X"))), EAnno(EAppAuto(EAnno(ELoc(2),TExists(2)), ELoc(3)), TGlob("A"))))
S |> pr
SType |> pr
cres = typerExecutor(Context([CExists(), CExists()]), S, SType) 
println("Type of $(S |> pr) is confirmed $(SType |> pr) in context $(cres .|> pr) !!!")
tres, cres = typerExecutor(Context([CExists(), CExists()]), S)
println("Type of $(S |> pr) is generated $(tres |> pr) in context $(cres .|> pr) !!!")



# Other more broken things:
gamma = Context([CExistsSolved(TGlob("K")), CExists()])
expr = EAbs(EGlobAuto("g"))
tc = typerExecutor(gamma, expr.body, TExists(2))

gamma = Context([CExistsSolved(TGlob("K")), CExists(), CExists(), CExistsSolved(TExists(2))])
tc = typerExecutor(gamma, ELoc(4), TExists(3))
# ^ buuh :(

typerExecutor(Context([CExistsSolved(TGlob("G"))]), EGlobAuto("f"))
typerExecutor(Context([CExistsSolved(TGlob("G"))]), ELoc(1))
typerExecutor(Context([CExists()]), ELoc(1))
typerExecutor(Context([]), EAppAuto(EAbs(EProd([ELoc(1), EGlobAuto("g")])), EGlobAuto("f")))
typerExecutor(Context([]), EAppAuto(EAbs(EProd([ELoc(1), EGlobAuto("g")])), EGlobAuto("f")))
typerExecutor(Context([]), EProd([EGlobAuto("f"), EGlobAuto("g")]), TForall(TProd([TLoc(1), TLoc(2)])))
c, e, t = Context([CExists(), CExistsSolved(TExists(1))]), EProd([ELoc(2)]), TForall(TProd([TLoc(1)]))
typerExecutor(c, e, t)
typerExecutor(Context([CExistsSolved(TGlob("K"))]), EAbs(EGlobAuto("g")))
# gamma = Context([CExistsSolved(TGlob("K"))])
# expr = EAbs(ELoc(1))
c = Context([CExists()])
e = EAnno(EAbs(EProd([ELoc(1), EGlobAuto("g")])), TForall(TFunAuto(TLoc(1), TProd([TLoc(1), TExists(1)]))))
EAnno(EAbs(EProd([ELoc(1), EGlobAuto("g")])), TForall(TFunAuto(TLoc(1), TProd([TLoc(1), TExists(1)])))) |>pr
