
Index = Int
Id = String
Error = String

abstract type Term end

abstract type CTerm <: Term end
abstract type ITerm <: CTerm end
# neutral term, i.e., a variable applied to a (possibly empty) sequence of values

########## Types

# Remember: (a+b) x (c+d) == axc + axd + bxc + bxd

struct TypeUniverse <: Term end
struct TTop <: Term end
struct TGlob <: ITerm # ITerm
    var::Id
    type::Term
end
struct TLocInt <: ITerm # ITerm ??????????????????
    var::Index
end
struct TAbs <: CTerm # CTerm
    body::CTerm
end
struct TAbsPi <: CTerm # CTerm
    var::CTerm
    body::CTerm
end
struct TApp <: ITerm
    # ops_dot_ordered::Array{Term}
    func::ITerm
    arg::CTerm
end
# struct TTerm <: Term
#     t_in::Term
#     t_out::Term
# end
struct TPi <: ITerm
    t_in::CTerm
    t_out::TAbs
end

struct TProd <: Term
    data::Array{Term}
end
struct TSum <: Term
    data::Array{Term}
end
struct TSumTerm <: Term
    tag::Index
    tag_name::String
    data::Term
end
struct TBranches <: Term
    ops_chances::Array{Term}
end
struct TAnno <: ITerm # ITerm
    expr::CTerm
    type::CTerm
end

# data Value
#    =  VLam      (Value -> Value)
#    |  VNeutral  Neutral
# data Neutral
#    =  NFree  Name
#    |  NApp   Neutral Value
# data Info
#    =  HasKind  Kind
#    |  HasType  Type
#   deriving (Show)
# type Env = [Value]
Context = Array{Term} # This would be a ELOC's CONTEXT !!!


function checkType(ctx, e::ITerm, ty)
    tye = inferType(ctx, e)
    (ty != ty') ? (Error("type mismatch")) : tye # NOTE: SYNTACTIC equality !!!!!  # Actually, they have some shanenigans w/ QUOTE functions
end
function checkType(ctx, e::TAbs, t::TPi)
    @assert t.t_in isa TProd
    checkSubst(t.t_in, e.body, TApp(t.t_out, TLocInt(i))) # OR SOMETHING with ctx's, "i" has no meaning here ...
end
function checkType(ctx, e, ty) Error("type mismatch") end
# MISSING: TProd, TSum, TTerm, etc, UNLESS they are inferrable ....


function inferType(ctx, e::EAnno)
    e, ty = e.expr, e.type
    checkType(ctx, ty, TypeUniverse())
    ty = reduc(TApp(tyt, [ctx[1]]))  # in fun(arg) form  # OR just use subst?
    checkType(ctx, e, ty)
    return ty
end
function inferType(ctx, e::TLocInt)
    if (ty = ctx[e.var]) !== nothing
       return ty
    else
       Error("unknown identifier")
    end
end
function inferType(ctx, e::TApp)
    e1, e2 = e.ops_dot_ordered[2], e.ops_dot_ordered[1]
    si = inferType(ctx, e1)
    if !(si isa TPi) return Error("illegal application") end
    checkType(ctx, e2, si.t_in)
    return reduc(TApp(si.t_out, e2))  # in fun(arg) form  # SHOULD pre reduc e2 as well ?
end

function inferType(ctx, t::TPi)
    tyt, tyt2 = t.t_in, t.t_out
    checkType(ctx, tyt, TypeUniverse())
    ty = subst(ctx[1], tyt)  # Or some shit
    checkType(vcat(["smthg", ty], ctx), subst([TLocInt(1)], tyt2), TypeUniverse())  # OR SOME SHIT
    return TypeUniverse()
end



Base.:(==)(a::TGlob, b::TGlob) = Base.:(==)(a.var, b.var)
Base.:(==)(a::TLocInt, b::TLocInt) = Base.:(==)(a.var, b.var)
Base.:(==)(a::TAbs, b::TAbs) = Base.:(==)(a.body, b.body)
Base.:(==)(a::TApp, b::TApp) = all(a.ops_dot_ordered .== b.ops_dot_ordered)
# Base.:(==)(a::TTerm, b::TTerm) = (a.t_in == b.t_in) && (a.t_out == b.t_out)
Base.:(==)(a::TPi, b::TPi) = (a.t_in == b.t_in) && (a.t_out == b.t_out)
Base.:(==)(a::TProd, b::TProd) = Base.:(==)(a.data, b.data)
Base.:(==)(a::TSum, b::TSum) = Base.:(==)(a.data, b.data)
Base.:(==)(a::TSumTerm, b::TSumTerm) = (a.data == b.data) && (a.tag == b.tag)



# Type functions


# TFunAuto(tin, tout) = TTerm(tin, tout)
# TTermAuto(tin, tout) = TTerm(TProd([tin]), tout)
TAppAuto(tfun, targ) = TApp([TProd([targ]), tfun])
TAppSwitch(func, args) = TApp([args, func])
TGlob(var::Id) = TGlob(var, TypeUniverse())
TGlobAuto(var::Id) = TGlob(var, TGlob(uppercase(var)))


subst(news::Array{Term}, t::TGlob)::Term= t
subst(news::Array{Term}, t::TLocInt)::Term = if t.var <= length(news) news[t.var] else throw(DomainError("Undefined local var $(t.var), n args given = $(length(news))" )) end
subst(news::Array{Term}, t::TTop)::Term = t
# subst(news::Array{Term}, t::TTerm)::Term = TTerm(subst(news, t.t_in), subst(news, t.t_out))
subst(news::Array{Term}, t::TPi)::Term = TPi(subst(news, t.t_in), TAbs(subst(vcat([TLocInt(1)], news), t.t_out.body))) # This EITHER COMPLETELY BREAKS, or ALLOWS partial application.. or Something...
subst(news::Array{Term}, t::TAbs)::Term = t
subst(news::Array{Term}, t::TProd)::Term = TProd(t.data .|> (x->subst(news, x)))
subst(news::Array{Term}, t::TSum)::Term = TSum(t.data .|> (x->subst(news, x)))
subst(news::Array{Term}, t::TApp)::Term = TApp(t.ops_dot_ordered .|> x->subst(news, x))
subst(news::Array{Term}, t::TSumTerm)::Term = TSumTerm(t.tag, t.tag_name, subst(news, t.data))
subst(news::Array{Term}, t::TAnno)::Term = TAnno(subst(news, t.Term), t.type)
subst(news::Array{Term}, t::TBranches)::Term = TBranches(t.ops_chances .|> x->subst(news, x)) # Just like TApp, This should have No effect being all TAbs's, but just in case.

reduc(t::TGlob)::Term = t
reduc(t::TLocInt)::Term = t
reduc(t::TTop)::Term = t
# reduc(t::TTerm)::Term = TTerm(t.t_in |> reduc, t.t_out |> reduc)
reduc(t::TPi)::Term = TPi(t.t_in |> reduc, TApp(t.t_out) |> reduc)
reduc(t::TAbs)::Term = TAbs(reduc(t.body))
reduc(t::TApp)::Term = reduc(Array{Term}(t.ops_dot_ordered .|> reduc)) # TApp is AN OBJECT THAT REPRESENTS A COMPUTATION (it's only "reduc" here since which one is "typechecked at runtime")
reduc(t::TProd)::Term = TProd(t.data .|> reduc)
reduc(t::TSum)::Term = TSum(t.data .|> reduc)
reduc(t::TSumTerm)::Term = TSumTerm(t.tag, t.tag_name, t.data |> reduc)
reduc(t::TAnno)::Term = TAnno(t.expr |> reduc, t.type)
reduc(t::TBranches)::Term = TBranches(t.ops_chances .|> reduc)
function reduc(ops::Array{Term})::Term
    #println("> doing the ", typeof(func),  " ", typeof(arg), " thing")
    # if ops[1] isa TAbs ops[1] = reduc(Array{Term}([TProd([]), ops[1]])) end # this is because i still havent decided between prods and 0-arg'd lambda's.
    #^ this MIGHT VERY WELL FAIL, idk
    while (length(ops) >= 2)
        ops1, ops2 = (ops[1] isa TAnno ? ops[1].expr : ops[1]), (ops[2] isa TAnno ? ops[2].expr : ops[2])
        if (ops1 isa TProd && ops2 isa TAbs)
            ops = vcat(Array{Term}([subst(ops1.data, ops2.body) |> reduc]), ops[3:end])
        elseif (ops1 isa TSumTerm && ops2 isa TBranches)
            ops = vcat([TApp([ops1.data, ops2.ops_chances[ops1.tag]]) |> reduc], ops[3:end])
        else break
        end
    end
    # TODO: make this into a more reasonable stack
    # TODO: Make it, you know, ACTUALLY compiled ? If it's even possible?  # --wdyk, maybe it's NOT and this is where the actual recursive-turingcompletey-selflooping-level-y interpreter comes in !!
    # TODO: DEFINITELY possible: Boy this is a mess, tidy upp your PRIMITIVES man !!!
    return length(ops) >= 2 ? TApp(ops) : ops[1]
end


pr_T(x::TGlob)::String = "$(x.var)"
pr_T(x::TLocInt)::String = "T$(x.var)"
pr_T(x::TTop)::String = "⊥"
# pr_T(x::TExists)::String = "∃$(x.var)"
pr_T(x::TAbs)::String = "∀($(x.body |> pr_T))" #(arity(x.body) > 0) ? ("∀($(x.body |> pr_T))") : (x.body |> pr_T)
function pr_T(x::TProd; is_an_arg::Bool = false)::String
    if is_an_arg
        join(x.data .|> pr_T, " x ")
    elseif length(x.data) == 0
        is_an_arg ? "" : "1T"
    else
        "[$(join(x.data .|> pr_T, " x "))]"
    end
end
function pr_T(x::TTerm)::String
    if x.t_in isa TTerm
        return "(" * (x.t_in |> pr_T) * ")->" * (x.t_out|> pr_T )
    elseif (x.t_in isa TProd && x.t_in.data |> length == 1 && x.t_in.data[1] isa TTerm)
        return "(" * (pr_T(x.t_in; is_an_arg=true)) * ")->" * (x.t_out|> pr_T )
    elseif (x.t_in isa TProd && x.t_in.data |> length == 1)
        return (pr_T(x.t_in; is_an_arg=true)) * "->" * (x.t_out|> pr_T )
    else return (x.t_in |> pr_T) * "->" *( x.t_out|> pr_T)
    end
end
function pr_T(x::TSumTerm)::String
    if x.data isa TProd
        return x.tag_name * "($(pr_T(x.data; is_an_arg=true)))"
    else
        return x.tag_name * "($(x.data |> pr_T))"
    end
end
pr_T(x::TSum)::String = "($(join(x.data .|> pr_T, " + ")))"
function pr_T(x::TApp)::String
    if length(x.ops_dot_ordered) == 2
        arg, func = x.ops_dot_ordered[1], x.ops_dot_ordered[2]
        # arg = (arg isa TProd && length(arg.data)==1) ? (arg.data[1] |> pr_T) : (arg |> pr_T)
        arg = (arg isa TProd) ? (arg |> pr_T)[2:end-1] : (arg |> pr_T)
        pr_T(func) * "(" * arg * ")"
    elseif length(x.ops_dot_ordered) <= 1
        throw(DomainError("howw $(x)"))
    else
        x.ops_dot_ordered .|> pr_T |> x->join(x, ".") |> (x->"[Ap $(x)]")
    end
end
pr_T(xs::Array{Term}) = xs .|> pr_T
pr_T(x::TBranches)::String = "{" * (["$(i)_-->$(e|>pr_T)" for (i,e) in enumerate(x.ops_chances)] |> (s->join(s, ", "))) * ")"
pr_T(x::TAnno)::String = "$(pr_E(x.expr)):$(pr_T(x.type))" # Hellloo...


pr_E(x::TGlob)::String = "$(x.var)"
pr_E(x::TLocInt)::String = "$(x.var)"
pr_E(x::TTop)::String = "T"
# pr_E(x::TApp)::String = "(" * pr_E(x.arg) * " ." * pr_E(x.func) *")" # join(x.func .|> pr_E, ".")
pr_E(x::TAbs)::String = "/{$(pr_E(x.body))}"
pr_E(x::TProd)::String = "[$(join(x.data .|> pr_E, ", "))]"
pr_E(x::TSumTerm)::String = "$(x.tag)_$(pr_E(x.data))"
pr_E(x::TBranches)::String = "{" * (["$(i)_-->$(e|>pr_E)" for (i,e) in enumerate(x.ops_chances)] |> (s->join(s, ", "))) * ")"
pr_E(x::TAnno)::String = "$(pr_E(x.expr)):$(pr_E(x.type))"
function pr_E(x::TApp)::String
    if length(x.ops_dot_ordered) == 2
        arg, func = x.ops_dot_ordered[1], x.ops_dot_ordered[2]
        # arg = (arg isa TProd && length(arg.data)==1) ? (arg.data[1] |> pr_E) : (arg |> pr_E)
        arg = (arg isa TProd) ? (arg |> pr_E)[2:end-1] : (arg |> pr_E)
        pr_E(func) * "(" * arg * ")"
    elseif length(x.ops_dot_ordered) <= 1
        throw(DomainError("howw $(x)"))
    else
        x.ops_dot_ordered .|> pr_E |> x->join(x, ".")
    end
end

pr(x) = pr_T(x)


# NOT used by the above:
arity(base::Index, t::TGlob)::Index= base
arity(base::Index, t::TLocInt)::Index = max(base, t.var)
arity(base::Index, t::TTop)::Index = base
arity(base::Index, t::TApp)::Index = t.ops_dot_ordered .|> (x->arity(base, x)) |> maximum
arity(base::Index, t::TTerm)::Index = [t.t_in, t.t_out] .|> (x->arity(base, x)) |> maximum
arity(base::Index, t::TAbs)::Index = base # Lam(arity(base, t.body))
arity(base::Index, t::TProd)::Index = t.data .|> (x->arity(base, x)) |> (x->maximum(x, init=0))
arity(base::Index, t::TSum)::Index = t.data .|> (x->arity(base, x)) |> (x->maximum(x, init=0))
arity(base::Index, t::TSumTerm)::Index = arity(base, t.data)
arity(base::Index, t::TAnno)::Index = arity(base, t.expr)
arity(base::Index, t::TBranches)::Index = t.ops_chances .|> (x->arity(base, x)) |> maximum
arity(base::Index, t::TSumTerm)::Index = arity(base, t.data)
arity(t::Term)::Index = arity(0, t)












# TTop TTop
# TGlob TGlob
# TLocInt TLocInt
# TAbs TAbs
# TApp TApp
# TTerm TTerm
# TProd TProd
# TSum TSum
# TSumTerm TSumTerm
# TBranches TBranches
# TAnno TAnno
# EGlobAuto TGlobAuto
# EAppSwitch TAppSwitch
# EAppAuto TAppAuto







S = TAbs(TAppAuto(TAppAuto(TLocInt(1), TLocInt(3)), TAppAuto(TLocInt(2), TLocInt(3))))
pr(S)

reduc(TAbs(TAppSwitch(S, TProd([TGlobAuto("f"), TGlobAuto("g"), TGlobAuto("x")])))) |> pr

f = TAbs(TLocInt(1))
g = TAbs(TGlobAuto("y"))
reduc(TAppSwitch(S, TProd([f, g, TGlobAuto("x")]))) |> pr

# Remember: At this point (not typechecked) it IS possible to be recursive!
ycomb = TAbs(TApp([TLocInt(1), TLocInt(1)]))
reduc(TApp([ycomb, ycomb])) |> pr

# EVEN IF, note that we ARE amart enough to not go ahead at inf, which is Good!
# I think it's because we are secretly a Fix, ie when TApp|>reduc is same as itself, we STOP


# Sum types 1. : CASE: ( i e ending on a single type C)
f = TAbs(TGlob("cdef", TGlob("C")))
g = TAbs(TLocInt(1))

e = TSumTerm(1, "1", TProd([TGlob("cpass", TGlob("C"))]))
case2 = TAbs(TApp([TLocInt(1), TBranches([TLocInt(2), TLocInt(3)])]))  # Case 2 meaning a sum of 2 types

reduc(TApp([TProd([e,f,g]), case2]))

# Sum types 2. : IF: ( i e on 1+1)

Tbool = TSum([TProd([]), TProd([])])
if_ = TAbs(TApp([TAnno(TApp([TLocInt(2), TLocInt(1)]), Tbool), TBranches([TApp([TLocInt(1), TLocInt(3)]), TApp([TLocInt(1), TLocInt(4)])])]))
# What THIS WOULD REQUIRE is, a POP/PartialApp to say that NO, you are Not interested in ^^ what comes out of Tbool, ONLY as a redirection !!
# Well, EITHER that, OR the (A+B)xC --> (AxC)+(BxC) function: i THINK you can use that as well, if you look closely !!
# if_ = TAbs(TApp([
#     TProd([TLocInt(1), TAnno(TApp([TLocInt(2), TLocInt(1)]), Tbool)]),
#     magic_distr_func,
#     magic_remove_dumb_1x_func,
#     TBranches([TLocInt(3), TLocInt(4)])
# ]))
# infer_type_rec(if_).res_type |> pr


TGlob("x", TGlob("A"))
TAnno(TLocInt(1), TFunAuto(TGlob("A"), TGlob("B")))
TAnno(TLocInt(2), TAbs(TLocInt(1)))

SType1 = TFunAuto(TGlob("X"), TGlob("A"))
SType2 = TFunAuto(TGlob("X"), TFunAuto(TGlob("A"), TGlob("B")))
SType = TFunAuto(TProd([SType2, SType1, TGlob("X")]), TGlob("B"))
SType |> pr

TGlob("S", TFunAuto(TGlob("A"), TGlob("B"))) |> pr
TFunAuto(TGlob("A"), TGlob("B")) |> pr

# Now polymorphicly:
SType1P = TFunAuto(TLocInt(3), TLocInt(2))
SType2P = TFunAuto(TLocInt(3), TFunAuto(TLocInt(2), TLocInt(1)))
STypeP = TAbs(TTerm(TProd([SType2P, SType1P, TLocInt(3)]), TLocInt(1)))
STypeP |> pr



