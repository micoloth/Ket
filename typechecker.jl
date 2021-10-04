# old ramblings about a typechecker, from "unification.jl"

TOPFREE=100
newvar() = (global TOPFREE = TOPFREE + 1; string(TOPFREE))

abstract type Term end
Id = String
Index = Int

struct FreeVar <: Term n::Id end
# struct LocalVar <: Term n::Index end
struct MetaVar <: Term n::Id end #still don't know
struct Uni <: Term n::Type{Term} end

struct Ap <: Term # goddammit i hate this
    l::Term
    r::Term
end
struct Concat <: Term # goddammit i hate this
    first::Term
    second::Term
end
struct Lam <: Term body::Term end
struct Prod <: Term terms::Array{Term} end
struct Pi <: Term
    from::Term
    to::Term # the to in the type of a Prod is a Prod iteself! Neato huh?
end

pr(x::FreeVar)::String = "F$(x.n)"
# pr(x::LocalVar)::String = "_$(x.n)"
pr(x::MetaVar)::String = "M$(x.n)"
# pr(x::Uni)::String = "T"
pr(x::Ap)::String = "("*pr(x.l)*" "*pr(x.r)*")"
pr(x::Lam)::String = "/{"*pr(x.body)*"}"
pr(x::Prod)::String = x.terms .|> pr |> (s->join(", ", s)) |> s->"[$(s)]"
pr(x::Pi)::String = "("*pr(x.from)*"->"*pr(x.to)*")"

pr(Ap(Lam(FreeVar("1")), FreeVar("2")))



abstract type RelFactInst end

struct EqFactInst <: RelFactInst
    l::Term
    r::Term
end

struct MetaType_ref
    ofTerm::Term
end
struct MetaType_any_new
    id::Int
end
MetaType = Union{MetaType_ref, MetaType_any_new}


struct TypedTerm <: RelFactInst
    term::Term
    type::Union{Term, MetaType}
end
struct ComputesToInst <: RelFactInst
    term::Term
    type::Term
end

abstract type RelConstrInst end

struct EqConstrInst <: RelConstrInst
    l::Term
    r::Term
end
struct IsaConstrInst <: RelConstrInst
    term::Term
    type::Term
end

Error=String

struct CheckedTerm_
    typedTerm::TypedTerm
    constrs::Array{RelConstrInst}
end
CheckedTerm = Union{CheckedTerm_, Error}

function typeCheckBind(func, c::CheckedTerm)::CheckedTerm
    # func is currently TypedTerm -> CheckedTerm_
    if typeof(c) === Error return c end
    ct = func(c.typedTerm)
    if typeof(ct) === Error return ct end
    return CheckedTerm_(ct.typedTerm, vcat(c.constrs, ct.constrs))
end

function typeCheckBind(func, c1::CheckedTerm, c2::CheckedTerm)::CheckedTerm
    # func is currently (TypedTerm x TypedTerm) -> CheckedTerm_
    if typeof(c1) === Error return c1 end
    if typeof(c2) === Error return c2 end
    ct = func(c1.typedTerm, c2.typedTerm)
    if typeof(ct) === Error return ct end
    return CheckedTerm_(ct.typedTerm, vcat(c1.constrs, c2.constrs, ct.constrs))
end

function typeOfConcat(first_tt::TypedTerm, second_tt::TypedTerm)::CheckedTerm
    constrs::Array{EqConstrInst} = [EqConstrInst(first_tt.type.to, second_tt.type.from)]
    if typeof(first_tt.type) !== Pi
        return Error("first_tt type $(pr(first_tt.type)) should be a Pi")
    elseif typeof(first_tt.type) === MetaType
        push!(constrs, EqConstrInst(first_tt.type, Pi(MetaVar(newvar()), MetaVar(newvar()))))  # TO MAKE BETTER

    elseif typeof(second_tt.type) !== Pi
        Error("second_tt type $(pr(second_tt.type)) should be a Pi")
    else CheckedTerm_(
        constrs,
        TypedTerm(Concat(first_tt.term, second_tt.type), Uni),
        )
    end
end

typeOf(t::Concat)::CheckedTerm = typeCheckBind(typeOfConcat, typeOf(t.first), typeOf(t.second))  # also written: t .|typeOf .TC typeOfConcat


function typeOfLambda(body_tt::TypedTerm)::CheckedTerm
    if typeof(body_tt.term) !== Concat
        Error("what, you crazy at not having $(pr(body_tt.term)) beig a concat????")
    else
        CheckedTerm_(
            TypedTerm(Pi(first_tt.term, second_tt.type), Uni),
            EqConstrInst(first_tt.type.to, second_tt.type.from)
            )
    end
end

typeOf(t::Lam)::CheckedTerm = typeCheckBind(typeOfLambda, typeOf(t.body))


Context = Dict{Id, Term}()

function typeOfVar(n::Id)::CheckedTerm
    res = get(Context, n, MetaVar())
end



isGood(n) = (if n<5 "Y" else "N" end)
isGood(1)
############################################################### types

# typeOf(t::LocalVar)::TypeRes = Error("wait you can't type Local Vars??? ($(t.n))")
# typeOf(t::Uni)::TypeRes = TypeRes_(Uni(Term), [])
typeOf(t::FreeVar)::TypeRes= (r = get(ctx, t.n, Nothing); r!==Nothing ? TypeRes_(r, []) : Error("Undefined var: $(pr(t))"))
# typeOf(t::MetaVar)::TypeRes = (r = get(mctx, t.n, Nothing); r!==Nothing ? TypeRes_(r, []) : Error("Undefined var: $(pr(t))"))
function typeOf(t::Ap)::CheckedTerm
    tpl, tpr = typeOf(t.l), typeOf(t.r)
    if typeof(tpl.type) === Pi
        TypeRes_(subst(t.r, 0, tpl.type.to), vcat(tpl.cs, tpr.cs, [Constraint(tpl.type.from, tpr.type)]))
    else
        m1, m2 = MetaVar(newvar()), MetaVar(newvar())
        TypeRes_(Ap(m2, t.r), vcat(tpl.cs, tpr.cs, [Constraint(tpr.type, m1), Constraint(tpl.type, Pi(m1, Ap(m2, LocalVar(0))))]))
    end
end

function typeOf(t::Lam)::TypeRes
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

function typeOf(t::Pi)::TypeRes
    v = newvar()
    tpfrom = typeOf(ctx, mctx, t.from)
    if typeof(tpfrom) === Error return tpfrom end
    ctx[v] = t.from
    tpto = typeOf(ctx, mctx, subst(Freevar(v), 0, t.to))
    pop!(ctx, v)
    if typeof(tpto) === Error return tpto end
    return TypeRes_(Unit(Term), vcat(tpfrom.cs, tpto.cs, [Constraint(Uni(Term), tpfrom.type), Constraint(Uni(Term), tpto.type)]))
end


