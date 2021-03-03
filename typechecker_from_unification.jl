
# slightly newer ramblings about a typechecker, from "unification.jl"
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
end
struct Prod <: Term
    data::Array{Term}
end
struct Sum <: Term
    data::Term
    tag::Index
end
struct Match <: Term
    funcs::Array{Term} # it breaks here: ASSUMPTION: each one computes a Lambda!!!!!!!!!
end


#############################################

struct TypeRes_
    type::Term
    cs::Array{Constraint}
end
TypeRes = Union{Error, TypeRes_}

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

typeOf(ctx::Dict{Id, Term}, t::LocalVar)::TypeRes = Error("wait you can't type Local Vars??? ($(t.n))")
typeOf(ctx::Dict{Id, Term}, t::Uni)::TypeRes = TypeRes_(Uni(Term), [])
typeOf(ctx::Dict{Id, Term}, t::FreeVar)::TypeRes= (r = get(ctx, t.n, Nothing); r!==Nothing ? TypeRes_(r, []) : Error("Undefined var: $(pr(t))"))
function typeOf(ctx::Dict{Id, Term}, t::Ap)::TypeRes
    tpl, tpr = typeOf(ctx, t.l), typeOf(ctx, t.r)
    if typeof(tpl) === Error return tpl end
    if typeof(tpr) === Error return tpr end
    if typeof(tpl.type) === Pi
        TypeRes_(subst(t.r, 0, tpl.type.to), vcat(tpl.cs, tpr.cs, [Constraint(tpl.type.from, tpr.type)]))
    else
        m1, m2 = MetaVar(newvar()), MetaVar(newvar())
        TypeRes_(Ap(m2, t.r), vcat(tpl.cs, tpr.cs, [Constraint(tpr.type, m1), Constraint(tpl.type, Pi(m1, Ap(m2, LocalVar(0))))]))
    end
end

function typeOf(ctx::Dict{Id, Term}, t::Lam)::TypeRes 
    v, m = newvar(), newvar()
    ctx[v] = MetaVar(m)
    mctx[m] = Uni(Term)
    typeres = typeOf(ctx, subst(FreeVar(v), 0, t.body))
    pop!(ctx, v)
    pop!(m)
    if typeof(typeres) === Error return typeres end
    return TypeRes_(Pi(MetaVar(m), substFV(LocalVar(0), v, raise(1, typeres.type))), 
                    vcat(typeres.cs, [Constraint(MetaVar(m), MetaVar(m))]))
end 
     
function typeOf(ctx::Dict{Id, Term}, t::Pi)::TypeRes
    v = newvar()
    tpfrom = typeOf(ctx, t.from)
    if typeof(tpfrom) === Error return tpfrom end
    ctx[v] = t.from
    tpto = typeOf(ctx, subst(Freevar(v), 0, t.to))
    pop!(ctx, v)
    if typeof(tpto) === Error return tpto end
    return TypeRes_(Unit(Term), vcat(tpfrom.cs, tpto.cs, [Constraint(Uni(Term), tpfrom.type), Constraint(Uni(Term), tpto.type)]))
end


function test_typeof(t::Term)
    println("Term: ", pr(t))
    tr=typeOf(ctx, t)
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
