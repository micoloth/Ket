
# higher order bidirectional typechecker, copied from :

# https://github.com/ollef/Bidirectional

TOPFREE=100
newvar() = "v" * string(global TOPFREE = TOPFREE + 1)

abstract type Expr end
Id = String
Var = Id
Index = Int

struct EVar <: Expr n::Id end
struct EUnit <: Expr n::Type{Expr} end
struct EApp <: Expr
    func::Expr # must compute to a lambda
    arg::Expr # must compute to a PROD
end
struct EAbs <: Expr # lambda, for some reason
    var::Var 
    body::Expr 
end
struct EAnno <: Expr # ANNOTATION syntax
    expr::Expr
    type::Expr # Polytype ???
end

# function subst(new::Expr, var::EVar, expr::Expr)::Expr
subst(new::Expr, var::Id, expr::EUnit)::Expr = expr 
subst(new::Expr, var::Id, expr::EApp)::Expr = EApp(subst(new, var, expr.func), subst(new, var, expr.arg)) 
subst(new::Expr, var::Id, expr::EAnno)::Expr = EAnno(subst(new, var, expr.expr), type) 
subst(new::Expr, var::Id, expr::EVar)::Expr = (expr.n == var ? new : expr)
function subst(new::Expr, var::Id, expr::EAbs)::Expr
    if expr.var == var expr
    else EAbs(expr.var, subst(new, var, expr.body))
    end
end

# TEST
subst(EVar("f"), "x", EAbs("x", EApp(EVar("x"), EVar("y"))))

# var -constructor for EVar
# eunit  -constructor for EUnit
# eabs  -constructor for EAbs
# ($$)  -constructor for EApp ( i guess he is redefining)
# (-:)  (means ":") -constructor for EAnno ( i guess he is redefining ?)

Tvar = String
# Var -string 
# TVar -string 



# a GADT is A BUNCH OF CONSTRUCTORS FOR A PARAMETRIC TYPE (so ythat you limit its shapes). 
# Each of these constructors returns "a function from TypeKind to some kind of type level object",
# this stuff is called Type and it's various ways to get a TypeKind-indexed type object.

# @enum TypeKind Mono Poly
# Polytype = Type(Poly)
# Monotype = Type(Mono)
# their signature: c(smth::Smth) = g   where  g(x::TypeKind)::Type

# What I'm gonna do:
abstract type Type_ end  # Type is reserved word
abstract type Polytype <: Type_ end
abstract type Monotype <: Polytype end

# --   "Only Polytypes can have foralls."
struct TVar_ <: Monotype  # this is the TYPE CONSTRUCTOR TVar, != from Tvar==String
    var::Tvar 
end
struct TUnit_ <: Monotype end
struct TExists_ <: Monotype
    var::Tvar
end
struct TForall_ <: Polytype
    arg::Tvar
    body::Polytype
end
struct TFun_Mono <: Monotype
    t1::Monotype
    t2::Monotype
end
struct TFun_Poly <: Polytype
    t1::Polytype
    t2::Polytype
end


# --   "Only Polytypes can have foralls."
TUnit()::Monotype = TUnit_() # whatever i don't care
TVar(var::Tvar)::Monotype = TVar_(var)
TExists(var::Tvar)::Monotype = TExists_(var)
TForall(arg::Tvar, body::Polytype)::TForall_ = TForall_(arg, body)
TFun(t1::Monotype, t2::Monotype)::TFun_Mono = TFun_Mono(t1, t2)
TFun(t1::Polytype, t2::Polytype)::TFun_Poly = TFun_Poly(t1, t2)

# TEST
TForall("x", TFun(TVar("x"), TVar("y")))
TForall("x", TFun(TVar("x"), TForall("y", TExists("z"))))

# TVar holds a str
# TFun: 1 and 2
# TForall: arg and body
# TUnit_ itself
# TExists: a string

#########
# -- Smart constructors
# tunit = TUnit
# tvar = TypeVar(str)
# exists = TExists(str)
# tforall = TForall(Str)
# (-->) == TFun
# tforalls :: [TVar] -> Polytype -> Polytype  # <---------------- huuuuuuh
# tforalls = flip (foldr TForall)  # <---------------- huuuuuuh
#########


################## whaa broken
# is it mono?
monotype(t::TUnit_)::Union{Monotype, Nothing} = t # so yes, in its weird way
monotype(t::TVar_)::Union{Monotype, Nothing} = t # so yes
monotype(t::TForall_)::Union{Monotype, Nothing} = nothing # so no
monotype(t::TExists_)::Union{Monotype, Nothing} = t # so yes
function monotype(t::TFun_Poly)::Union{Monotype, Nothing} # WHEN should even this be not nothing COME ON
    t1=monotype(t.t1); t2=monotype(t.t2); 
    (t1!==nothing && t2!==nothing) ?  TFun(t1, t2) : nothing  # so maybe
end
function monotype(t::TFun_Mono)::Union{Monotype, Nothing} 
    t1=monotype(t.t1); t2=monotype(t.t2); 
    (t1!==nothing && t2!==nothing) ?  TFun(t1, t2) : nothing  # so maybe
    # [t.1, t.2] .| monotype .{(x!==nothing and y!==nothing) ? TFun(x, y)}
    # [t.1, t.2] .| monotype = [t1, t2] in [t1, t2].all<{!==nothing}> .?TFun(t1, t2)
    # [t.1, t.2] .| monotype .if {x .| {not na} .all}-> TFun(x), else -> nothing
    # (not (1 or 1)) means (0 and 0)
end

# is it poly?
# polytype(t::TUnit())::Union{Monotype, Nothing} = TUnit() # so yes, ??????
# polytype(t::TVar)::Union{Monotype, Nothing} = t # so yes ??????
# polytype(t::TForall)::Union{Monotype, Nothing} = t # so yes
# polytype(t::TExists)::Union{Monotype, Nothing} = t # so yes ??????
# polytype(t::TFun)::Union{Monotype, Nothing} = TFun(polytype(t.t1), polytype(t.t2)) # So maybe- but actually yes ???????????
################## whaa broken


# free vars 
freeTVars(t::TUnit_)::Array{Tvar} = []
freeTVars(t::TVar_)::Array{Tvar} = [t.var]
freeTVars(t::TForall_)::Array{Tvar} =  [v for v in freeTVars(t.body) if v!=t.arg]
freeTVars(t::TExists_)::Array{Tvar} =  [t.var]
freeTVars(t::TFun_Poly)::Array{Tvar} = vcat(freeTVars(t.t1), freeTVars(t.t2))
freeTVars(t::TFun_Mono)::Array{Tvar} = vcat(freeTVars(t.t1), freeTVars(t.t2))

# TEST
freeTVars(TForall("x", TFun(TVar("x"), TVar("y"))))

# typeSubst A α B = [A/α]B
# t'::Type    v::TVar     typ::Type  # < what they use
# new::Type   var::TVar   expr::Type
typeSubst(new::Type_, var::Tvar, expr::TUnit_)::Type_ = expr
typeSubst(new::Type_, var::Tvar, expr::TVar_)::Type_ = (expr.var == var ? new : expr)
typeSubst(new::Type_, var::Tvar, expr::TExists_)::Type_ = (expr.var == var ? new : expr)
typeSubst(new::Type_, var::Tvar, expr::TFun_Poly)::Type_ = TFun_Poly(typeSubst(new, var, expr.t1), typeSubst(new, var, expr.t2))
typeSubst(new::Type_, var::Tvar, expr::TFun_Mono)::Type_ = TFun_Mono(typeSubst(new, var, expr.t1), typeSubst(new, var, expr.t2))
function typeSubst(new::Type_, var::Tvar, expr::TForall_)::Type_
    if expr.arg == var expr
    else TForall(expr.arg, typeSubst(new, var, expr.body))
    end
end

# TEST
typeSubst(TExists("g"), "k", TForall("x", TExists("k")))
typeSubst(TExists("g"), "k", TFun_Mono(TVar("x"), TExists("k")))
typeSubst(TExists("g"), "k", TFun(TVar("x"), TExists("k")))
typeSubst(TExists("g"), "k", TForall("x", TFun(TVar("y"), TExists("k"))))

# typeSubsts :: [(Type a, TVar)] -> Type a -> Type a
# typeSubsts = flip $ foldr $ uncurry typeSubst # I'll prob get this later................    # <---------------- huuuuuuh


struct Complete end
struct Incomplete end
Complete() === Complete() # true
Complete() == Incomplete() # false
# their signature: c(smth::Smth) = g   where  g(x::ContextKind)::ContextElem 

# What I'm gonna do:
abstract type ContextElem{T} end  # Type is reserved word


# --   "Only Incomplete contexts can have unsolved existentials."
struct CForall_{T} <: ContextElem{T}
    var::Tvar
end
struct CVar_{T} <: ContextElem{T}
    var::Var
    type::Polytype
end
struct CExists_ <: ContextElem{Incomplete()}
    var::Tvar
end
struct CExistsSolved_{T} <: ContextElem{T}
    var::Tvar
    type::Monotype
end
struct CMarker_{T} <: ContextElem{T}
    var::Tvar
end

# TEST
CExists_("6") isa ContextElem
CExists_("6") isa ContextElem{Complete()}
CVar_{Incomplete()}("x", TForall("y", TVar("P")))

# --   "Only Incomplete contexts can have unsolved existentials."
# CForall(v::Tvar)::ContextElem = 5# smth  # remember, Tvar==String
# CVar(v::Tvar, t::PolyType)::ContextElem = 5# smth   # remember, Tvar==String
# CExists(v::Tvar, c::ContextElem)::ContextElem = 5Incomplete(##)  # <<<<<<<
# CExistsSolved(v::Tvar, t::Monotype)::ContextElem = 5# smth
# CMarker(v::Tvar)::ContextElem = 5  # smth

struct GContext{T}
    elements::Array{ContextElem{T}}    
end

# TEST
GContext{Complete()}([CExistsSolved_{Complete()}("6", TVar("x"))]) # ok
# GContext{Complete()}([CExists_("6")]) #ERROR (as it should)

Context = GContext{Incomplete()} 

# (>:) is just append to context
# (>++) is concat to context
# context :: [ContextElem a] -> GContext a   where   context = Context . reverse: constructor w/ reverse
# since a context is an array, it inserts a new, sure whatever
# dropMarker(m::ContextElem, g::Context) SHOULD remove m from g
# vcat(>,,(,i guess,rrays are in fact both a semigroup and a monoid (with concatenation). Jesus tho -.-)

function dropMarker(m::ContextElem{T}, g::GContext{T}) ::GContext{T}  where {T}
    i=findfirst(x->x==m, g.elements);
    (i===nothing) ? g : GContext{T}(deleteat!(g.elements, i))
end

function breakMarker(m::ContextElem{T}, g::GContext{T})::Tuple{GContext{T}, GContext{T}}  where {T}
    i=findfirst(x->x==m, g.elements);
    i = (i!==nothing) ? i : length(g.elements) + 1
    (GContext{T}(g.elements[1:i-1]), GContext{T}(g.elements[i+1:end]))
end

[1,2,3][1:0], [1,2,3][3+2:end]
findfirst((x->x==CExists_("x")), Array{ContextElem}([CExists_("y"), CExistsSolved_{Complete()}("x", TVar("4")), CExists_("x")]))
(c1, c2) = breakMarker(CExists_("x"), Context(
    [CExists_("y"), CExistsSolved_{Incomplete()}("x", TVar("4")), CExists_("x"), CForall_{Incomplete()}("4"), ]))
c1
c2

######################################################################################

# existential vars
existentials(t::CExists_)::Array{Tvar} = [t.var]
existentials(t::CExistsSolved_)::Array{Tvar} = [t.var]
existentials(t::CForall_)::Array{Tvar} = []
existentials(t::CVar_)::Array{Tvar} = []
existentials(t::CMarker_)::Array{Tvar} = []
existentials(gamma::Context)::Array{Tvar} = vcat([existentials(t) for t in gamma.elements]...)

# TEST
existentials(Context([CVar_{Incomplete()}("x", TExists("T")), CExists_("y")]))

# unsolved vars
unsolved(gamma::Context)::Array{Tvar} = vcat([unsolved(t) for t in gamma.elements]...)
unsolved(t::CExists_)::Array{Tvar} = [t.var]
unsolved(t)::Array{Tvar} = []

# TEST
unsolved(Context([CVar_{Incomplete()}("x", TExists("T")), CExists_("y")]))

# var vars
vars(gamma::Context)::Array{Tvar} = vcat([vars(t) for t in gamma.elements]...)
vars(t::CVar_)::Array{Tvar} = [t.var]
vars(t)::Array{Tvar} = []

# foralls vars
foralls(gamma::Context)::Array{Tvar} = vcat([foralls(t) for t in gamma.elements]...)
foralls(t::CForall_)::Array{Tvar} = [t.arg]
foralls(t)::Array{Tvar} = []

# markers vars
markers(gamma::Context)::Array{Tvar} = vcat([markers(t) for t in gamma.elements]...)
markers(t::CMarker_)::Array{Tvar} = [t.var]
markers(t)::Array{Tvar} = []


# -- | Well-formedness of types
# --   typewf Γ A <=> Γ |- A
typewf(gamma::Context, t::TVar_)::Bool = t.var in foralls(gamma)
typewf(gamma::Context, t::TUnit_)::Bool = true
typewf(gamma::Context, t::TFun_Mono)::Bool = typewf(gamma, t.t1) && typewf(gamma, t.t2)
typewf(gamma::Context, t::TFun_Poly)::Bool = typewf(gamma, t.t1) && typewf(gamma, t.t2)
typewf(gamma::Context, t::TForall_)::Bool = typewf(Context(vcat(gamma.elements, [CForall_{Incomplete()}(t.arg)])), t.body)
typewf(gamma::Context, t::TExists_)::Bool = t.var in existentials(gamma)



# -- | Well-formedness of contexts
# --   wf Γ <=> Γ ctx
function wf(gamma::Context)::Bool where {T}
    rev = gamma.elements
    # rev = reverse(gamma.elements)
    for (i, c) in enumerate(rev)
        # (i, c) = (1, rev[1])
        rest::Context = Context(rev[1:i-1])
        if !wf(rest, c) return false end
    end
    true
end
function wf(rest::Context, c::CForall_)::Bool !(c.arg in foralls(rest)) end
function wf(rest::Context, c::CVar_)::Bool ! (c.var in vars(rest)) && typewf(rest, c.type) end
function wf(rest::Context, c::CExists_)::Bool ! (c.var in existentials(rest)) end
function wf(rest::Context, c::CExistsSolved_)::Bool ! (c.var in existentials(rest)) && typewf(rest, c.type) end
function wf(rest::Context, c::CMarker_)::Bool !(c.var in markers(rest)) && !(c.var in existentials(rest)) end

wf(Context([CExists_("x"), CVar_{Incomplete()}("x", TExists("T"))])) # false, it seems


Error = String
# -- Assert-like functionality to make sure that contexts and types are well-formed
# These return either the obj itself or an error
function checkwf(gamma::Context, x)
    wf(gamma) ? x : Error("Malformed context: $(gamma)")
end
checkwftype(gamma::Context, t::Type_, x) = typewf(gamma, t) ? checkwf(gamma, x) : Error("Malformed type: $(t)") # pretty(t, gamma)


# -- | findSolved (ΓL,α^ = τ,ΓR) α = Just τ
function findSolved(gamma::Context, v::Tvar)::Union{Monotype, Nothing} 
    for c in gamma.elements
        if c isa CExistsSolved_ && v == c.var return c.type end
    end
    nothing
end
      
# -- findVarType (ΓL,x : A,ΓR) x = Just A
function findVarType(gamma::Context, v::Tvar)::Union{Polytype, Nothing} 
    for c in gamma.elements
        if c isa CVar_ && v == c.var return c.type end
    end
    nothing
end      

# -- | solve (ΓL,α^,ΓR) α τ = (ΓL,α = τ,ΓR)
# since a context is an array, it inserts a new CExistsSolved(var, type) where needed, granted everything on the left doesnt use it
function solve(gamma::Context, alpha::Tvar, tau::Monotype)::Union{Context, Nothing}  
    (gammaL, gammaR) = breakMarker(CExists_(alpha), gamma)
    gamma2 = Context(vcat(gammaL.elements, [CExistsSolved_{Incomplete()}(alpha, tau)], gammaR.elements))
    if typewf(gammaL, tau) gamma2
    else nothing
    end
end

# -- | insertAt (ΓL,c,ΓR) c Θ = ΓL,Θ,ΓR
# How do you insert in Julia?
insertAt(gamma:: Context, c::ContextElem{Incomplete()}, theta::Context)::Context = (
    (gammaL, gammaR) = breakMarker(c, gamma); Context(vcat(gammaL.elems, theta.elems, gammaR.elems)))


# apply(gamma:: Context, typ::Polytype)::Polytype
# why wasn't this around yet?
apply(gamma:: Context, typ::TUnit_)::Polytype = typ
apply(gamma:: Context, typ::TVar_)::Polytype = typ
apply(gamma:: Context, typ::TForall_)::Polytype = TForall(typ.arg, apply(gamma, typ.body))
apply(gamma:: Context, typ::TFun_Mono)::Polytype = TFun(apply(gamma, t.t1), apply(gamma, t.t2))
apply(gamma:: Context, typ::TFun_Poly)::Polytype = TFun(apply(gamma, t.t1), apply(gamma, t.t2))
function apply(gamma:: Context, typ::TExists_)::Polytype
    # maybe (TExists v) (apply gamma . polytype) $ findSolved gamma v
    # The maybe function takes a default value, a function, and a Maybe value. If the Maybe value is Nothing, the function returns the default value. Otherwise, it applies the function to the value inside the Just and returns the result.
    fs = findSolved(gamma, typ.var)
    (fs === nothing) ? typ : apply(gamma, fs) # should be converted to PolyType
end
ordered(gamma::Context, alpha::Tvar, beta::Tvar)::Bool = alpha in existentials(dropMarker(CExists_(beta), gamma))


############################################################################


# -- | Algorithmic subtyping:
# --   subtype Γ A B = Δ <=> Γ |- A <: B -| Δ

print(repr(EAbs("x", EApp(EVar("x"), EVar("y")))))
alpha=EAbs("x", EApp(EVar("x"), EVar("y")))
alpha2=EAbs("x", EApp(EVar("x"), EVar("y")))

err(alpha, alpha2) = Error("subtype, don't yet know what to do with: $(repr(alpha)), $(repr(alpha2))")

subtype_(gamma::Context, alpha::TVar_, alpha2::TVar_) = (alpha == alpha2 ? gamma : err(alpha, alpha2))
subtype_(gamma::Context, alpha::TUnit_, alpha2::TUnit_) = gamma
subtype_(gamma::Context, alpha::TExists_, alpha2::TExists_) = (alpha == alpha2 && alpha.var in existentials(gamma)) ? gamma : err(alpha, alpha2)
subtype_(gamma::Context, fa::TFun_Mono, fb::TFun_Mono) = (c=subtype(gamma, fb.t1, fa.t2); subtype(c, apply(c, fa.t2), apply(c, fb.t2)))
subtype_(gamma::Context, fa::TFun_Poly, fb::TFun_Poly) = (c=subtype(gamma, fb.t1, fa.t2); subtype(c, apply(c, fa.t2), apply(c, fb.t2)))
function subtype_(gamma::Context, a, t::TForall_)
    v = newvar()
    vc = CForall_{Incomplete()}(v)
    gamma2 = Context(push!(gamma.elements, vc))
    gamma_res = subtype(gamma2, a, typeSubst(TVar(v), t.arg, t.body))
    dropMarker(vc, gamma_res)
end
function subtype_(gamma::Context, a::TForall_, t::TForall_) # the same PREVIOUS case
    v = newvar()
    vc = CForall_{Incomplete()}(v)
    gamma2 = Context(push!(gamma.elements, vc))
    gamma_res = subtype(gamma2, a, typeSubst(TVar(v), t.arg, t.body))
    dropMarker(vc, gamma_res)
end
function subtype_(gamma::Context, t::TForall_, b)
    v = newvar()
    vc = CMarker_{Incomplete()}(v)
    gamma2 = Context(push!(gamma.elements, vc, CExist))
    gamma_res = subtype(gamma2, typeSubst(TExists_(v), t.arg, t.body), b)
    dropMarker(vc, gamma_res)
end
subtype_(gamma::Context, t::TExists_, a) = (t.var in existentials(gamma) && !(t.var in freeTVars(a))) ? instantiateL(gamma, t.var, a) : err(t,a)
subtype_(gamma::Context, t::TExists_, a::TExists_) = (t.var in existentials(gamma) && !(t.var in freeTVars(a))) ? instantiateL(gamma, t.var, a) : err(t,a)
# ^ the same PREVIOUS case
subtype_(gamma::Context, a, t::TExists_) = (t.var in existentials(gamma) && !(t.var in freeTVars(a))) ? instantiateR(gamma, a, t.var) : err(a,t)

subtype_(gamma, a, b) = err(a,b)


# -- | Algorithmic subtyping:
# --   subtype Γ A B = Δ <=> Γ |- A <: B -| Δ
function subtype(gamma::Context, typ1::Polytype, typ2::Polytype)::Union{Context, Error}
    newgamma = subtype_(gamma, typ1, typ2)
    newgamma = checkwftype(gamma, typ2, newgamma)
    if typeof(newgamma) == Error return newgamma end
    newgamma = checkwftype(gamma, typ1, newgamma)
    if typeof(newgamma) == Error return newgamma end
    print("Just checked: ", typ1, typ2)
    newgamma
end


# -- | Algorithmic instantiation (left):
# --   instantiateL Γ α A = Δ <=> Γ |- α^ :=< A -| Δ
function instantiateL(gamma::Context, alpha::Tvar, a::Polytype)::Union{Error, Context}
    if isa(a, Monotype)
       newgamma = solve(gamma, alpha, a)
       if newgamma !== nothing return newgamma end
    else
        newgamma = gamma
    end
    # whaaat
    instantiateL_(gamma, alpha, a)

    newgamma = instantiateL_(gamma, alpha, a)
    newgamma = checkwftype(gamma, TExists(alpha), newgamma)
    if typeof(newgamma) == Error return newgamma end
    newgamma = checkwftype(gamma, a, newgamma)
    if typeof(newgamma) == Error return newgamma end
    print("Just checked: ", alpha, a)
    newgamma
end

function instantiateL_(gamma::Context, alpha::Tvar, t::TExists_)::Union{Error, Context} 
    if ordered(gamma, alpha, t.var)
        solve(gamma, t.var, TExists_(alpha)) # should be ALWAYS NOT NOTHING
    else
        solve(gamma, alpha, TExists_(t.var)) # should be ALWAYS NOT NOTHING
    end
end

function instantiateL_(gamma::Context, alpha::Tvar, t::TFun_Poly)::Union{Error, Context} 
    alpha1 = newvar()
    alpha2 = newvar()
    c = Context([CExists_(alpha2), CExists_(alpha1), CExistsSolved_{Incomplete()}(alpha, TFun_Mono(TExists_(alpha1), TExists_(alpha2)))])
    theta = instantiateR(insertAt(gamma, CExists_(alpha), c), t.t1, alpha1)
    instantiateL(theta, alpha2, apply(theta, t.t2))
end
    
    
function instantiateL_(gamma::Context, alpha::Tvar, t::TForall_)::Union{Error, Context} 
    # TForall beta b -> do
    # -- Do alpha conversion to avoid clashes
    beta2 = newvar()
    beta2_c = CForall_{Incomplete()}(beta2)
    l = instantiateL(Context(vcat(gamma.elements, [beta2_c])), alpha, typeSubst(TVar_(beta2), beta, b))
    dropMarker(beta2_c, l)
    # {gamma .append<beta2 .CForall_>   }
    # {alpha                            } .instantiateL .?dropMarker<CForall_(beta2)>
    # {typeSubst(TVar_(beta2), beta, b) }
end

instantiateL_(gamma::Context, alpha::Tvar, t)::Union{Error, Context} = Error("The impossible happened! instantiateL: $(repr(alpha)), $(repr(a))")


# -- | Algorithmic instantiation (right):
# --   instantiateR Γ A α = Δ <=> Γ |- A =:< α -| Δ
function instantiateR_(gamma::Context, a::Polytype, alpha::Tvar)::Context
    # smthg smthg
    # traceNS "instantiateR" (gamma, a, alpha) $
    # checkwftype gamma a $ checkwftype gamma (TExists alpha) $
    # case solve gamma alpha =<< monotype a of
    #   Just gamma' -> return gamma'
    #   Nothing -> case a of
    #     -- InstRReach
end

function instantiateR_(gamma::Context, t::TExists_, alpha::Tvar)::Context  #IMPORTANT: Polytype
    if ordered(gamma, alpha, t.var)
        solve(gamma, t.var, TExists_(alpha)) # should be ALWAYS NOT NOTHING
    else
        solve(gamma, alpha, TExists_(t.var)) # should be ALWAYS NOT NOTHING
    end
end

function instantiateR_(gamma::Context, t::TFun_Poly, alpha::Tvar)::Context  #IMPORTANT: Polytype
    alpha1 = newvar()
    alpha2 = newvar()
    c = Context([CExists_(alpha2), CExists_(alpha1), CExistsSolved_{Incomplete()}(alpha, TFun_Mono(TExists_(alpha1), TExists_(alpha2)))])
    theta = instantiateL(insertAt(gamma, CExists_(alpha), c), alpha1, t.t1)
    instantiateR(theta, apply(theta, t.t2), alpha2)
end

function instantiateR_(gamma::Context, t::TForall_, alpha::Tvar)::Context  #IMPORTANT: Polytype
    # -- Do alpha conversion to avoid clashes
    beta2 = newvar()
    beta2_c = CMarker_{Incomplete()}(beta2)
    l = instantiateR(Context(vcat(gamma.elements, [beta2_c, CExists_(beta2)])), typeSubst(TExists(beta2), t.arg, t.body), alpha)
    dropMarker(beta2_c, l)
end
instantiateR_(gamma::Context, t, alpha::Tvar)::Union{Error, Context} = Error("The impossible happened! instantiateL: $(repr(alpha)), $(repr(a))")



TypecheckRes = Union{Error, Context}

# -- | Type checking:
# --   typecheck Γ e A = Δ <=> Γ |- e <= A -| Δ
function typecheck(gamma::Context, expr::Expr, typ::Polytype)::TypecheckRes
    tc = typecheck_(gamma, expr, typ)
    if (typeof(tc) === Error) return tc end
    tc = checkwftype(gamma, typ, tc)
    # print something about tc, expr and typ
    tc
end

function typecheck_(gamma::Context, expr::EUnit, typ::TUnit_)::TypecheckRes
    gamma
end

function typecheck_(gamma::Context, expr, typ::TForall_)::TypecheckRes
    # -- Do alpha conversion to avoid clashes
    alpha2 = newvar()
    alpha2_c = CForall_{Incomplete()}(alpha2)
    gamma2 = Context(vcat(gamma.elements, [alpha2_c]))
    gamma2 = typecheck(gamma2, expr, typeSubst(TVar(alpha2), typ.arg, typ.body))
    (typeof(gamma2) !== Error) ? dropMarker(alpha2_c, gamma2) : gamma2
end
   
function typecheck_(gamma::Context, expr::EAbs, typ::TFun_Mono)::TypecheckRes
    # -- Do alpha conversion to avoid clashes
    x2 = newvar()
    x2var = CVar_{Incomplete()}(x2, typ.t1)
    gamma2 = Context(vcat(gamma.elements, [x2var]))
    gamma2 = typecheck(gamma2, subst(EVar(x2), expr.var, expr.body), typ.t2)
    (typeof(gamma2) !== Error) ? dropMarker(x2var, gamma2) : gamma2
end

function typecheck_(gamma::Context, expr::EAbs, typ::TFun_Poly)::TypecheckRes # exactly the same^; ofc i think i need this
    # -- Do alpha conversion to avoid clashes
    x2 = newvar()
    x2var = CVar_{Incomplete()}(x2, typ.t1)
    gamma2 = Context(vcat(gamma.elements, [x2var]))
    gamma2 = typecheck(gamma2, subst(EVar(x2), expr.var, expr.body), typ.t2)
    (typeof(gamma2) !== Error) ? dropMarker(x2var, gamma2) : gamma2
end

function typecheck_(gamma::Context, expr, typ)::TypecheckRes
    res = typesynth(gamma, expr)
    if (typeof(res) === Error) return res end
    (a, theta) = res
    subtype(theta, apply(theta, a), apply(theta, typ))
end


TypesynthRes = Union{Error, Tuple{Polytype, Context}}


# -- | Type synthesising:
# --   typesynth Γ e = (A, Δ) <=> Γ |- e => A -| Δ
function typesynth(gamma::Context, expr::Expr)::TypesynthRes 
    tc = typesynth_(gamma, expr)
    if (typeof(tc) === Error) return tc end
    tc = checkwf(gamma, tc)
    # print something about tc and expr
    tc
end

function typesynth_(gamma::Context, expr::EVar)::TypesynthRes 
    t = findVarType(gamma, expr.n) 
    t = (t === nothing) ? Error("typesynth: not in scope: var $(expr), in $(gamma)") : t
    (t, gamma)
    # [gamma, expr.n] .findVarType .{nothing> Error(m), x> x} .{[x, gamma]} where m = "typesynth: not in scope: var $(expr), in $(gamma)"
end

function typesynth_(gamma::Context, expr::EAnno)::TypesynthRes 
    tc = typecheck(gamma, expr.expr, expr.type)
    (typeof(tc) !== Error) ? (expr.type, tc) : tc 
end

function typesynth_(gamma::Context, expr::EUnit)::TypesynthRes 
    (TUnit()(), gamma)
end

function typesynth_(gamma::Context, expr::EApp)::TypesynthRes 
    res = typesynth(gamma, expr.arg)  # OR func ?????????????? <------------------------------
    if (typeof(res) === Error) return res end
    (a, theta) = res
    typeapplysynth(theta, apply(theta, a), expr.func) # OR arg ????????????? <------------------------------
end

function typesynth_(gamma::Context, expr::EAbs)::TypesynthRes 
    x2 = newvar()
    alpha = newvar()
    beta = newvar()
    x2var = CVar_{Incomplete()}(x2, TExists(alpha))
    c = Context(vcat(gamma.elements, [CExists_(alpha), CExists_(beta), x2var]))
    tc = typecheck(c, subst(EVar(x2), expr.var, expr.body), TExists(beta))
    if (typeof(tc) === Error) return tc end
    delta = dropMarker(x2var, tc)
    (TFun_Mono(TExists(alpha), TExists(beta)), delta)
end


# function typesynth_(gamma::Context, expr::EAbs)::TypesynthRes 
#     # -- ->I=> Full Damas-Milner type inference
#     x2 = newvar()
#     alpha = newvar()
#     x2var = CVar_{Incomplete()}(x2, TExists(alpha))
#     beta = newvar()
#     c = Context(vcat(gamma.elements, [CMarker_{Incomplete()}(alpha), CExists_(alpha), CExists_(beta), x2var]))# different
#     tc = typecheck(c, subst(EVar(x2), expr.var, expr.body), TExists(beta))
#     (delta, delta2) = breakMarker(CMarker_{Incomplete()}(x2, TExists(alpha)), tc)
#     tau = apply(delta2, TFun_Mono(TExists(alpha), TExists(beta)))
#     evars = unsolved(delta2)
#     uvars = [newvar() for i in length(evars)]
#     for (evar, uvar) in zip(evars, uvars)
#         tau = typeSubst(TVar(uvar), evar, tau)
#     end
#     # tau is some poly Type
#     # -> tforalls uvars tau
#     # -> flip (foldr TForall) uvars tau
#     # where foldr f z (x:xs)
#     # so (foldr TForall) z (x:xs) becomes (foldr TForall) (x:xs) z
#     # -> foldr TForall uvars tau
#     for u in uvars:
#         tau = TForall(u, tau)
#     end
#     return (tau, delta)
# end



# -- | Type application synthesising
# --   typeapplysynth Γ A e = (C, Δ) <=> Γ |- A . e =>> C -| Δ
function typeapplysynth(gamma::Context, typ::Polytype, expr::Expr)::TypesynthRes
    tc = typeapplysynth_(gamma, typ, expr)
    if (typeof(tc) === Error) return tc end
    tc = checkwftype(gamma, typ, tc)
    # print something about tc and typ and expr
    tc
end

function typeapplysynth_(gamma::Context, typ::TForall_, expr::Expr)::TypesynthRes
    alpha2 = newvar()
    c = Context(vcat(gamma, [CExists_(alpha2)]))
    typeapplysynth(c, typeSubst(TExists(alpha2), typ.arg, typ.body), expr)
end

function typeapplysynth_(gamma::Context, typ::TExists_, expr::Expr)::TypesynthRes
    alpha1 = newvar()
    alpha2 = newvar()
    c = Context([CExists_(alpha2), CExists_(alpha1), CExistsSolved_{Incomplete()}(typ.var, TFun_Mono(TExists(alpha1), TExists(alpha2)))])
    cc = insertAt(gamma, CExists_(typ.var), c)
    delta = typecheck(cc, expr, TExists(alpha1))
    if (typeof(delta) === Error) return delta end
    (TExists(alpha2), delta)
end

function typeapplysynth_(gamma::Context, typ::TFun_Mono, expr::Expr)::TypesynthRes
    res = typecheck(gamma, expr, typ.t1)
    if (typeof(res) === Error) return res end
    (typ.t2, res)
end
    
function typeapplysynth_(gamma::Context, typ, expr::Expr)::TypesynthRes
    Error("typeapplysynth: don't know what to do with: $(gamma), $(typ), $(e)")
end
    

function typesynthClosed(e::Expr)::TypesynthRes
    res = typesynth(Context([]), e)
    if (typeof(res) === Error) return res end
    (a, gamma) = res
    (apply(gamma, a), gamma) 
end
    

cv = CVar_{Incomplete()}("x", TFun_Poly(TForall("x", TUnit()), TForall("y", TUnit())))
typesynth(Context([cv]), EVar("x"))


# eid :: Expr -- (λx. x) : ∀ t. t → t
# eid = eabs "x" (var "x") -: tforall "t" (tvar "t" --> tvar "t")


eid =EAbs("x", EVar("x"))
eid_T = TForall("t", TFun_Mono(TVar("t"), TVar("t")))
typesynth(Context([]), eid)


gamma = GContext{Incomplete()}(ContextElem{Incomplete()}[CExists_("v105"), CExists_("v106"), CVar_{Incomplete()}("v104", TExists_("v105"))])


# typesynth(Context([]), EAbs("x", EVar("x")))

# -- Examples
# eid :: Expr -- (λx. x) : ∀ t. t → t
# eid = eabs "x" (var "x") -: tforall "t" (tvar "t" --> tvar "t")
# -- Impredicative, so doesn't typecheck
# ididunit :: Expr -- (λid. id id ()) ((λx. x) : ∀ t. t → t)
# ididunit = eabs "id" (((var "id" -: tforall "t" (tvar "t" --> tvar "t"))  $$ var "id") $$ eunit) $$ eid
# idunit :: Expr -- (λid. id ()) ((λx. x) : ∀ t. t → t)
# idunit = eabs "id" (var "id" $$ eunit) $$ eid
# idid :: Expr -- id id
# idid = (eid $$ eid) -: tforall "t" (tvar "t" --> tvar "t")
