
Index = Int
Id = String
Error = String

abstract type Data end
abstract type Box end
abstract type Arrow end


########## Expres

struct ELoc <: Arrow n::Index end
struct EGlob <: Arrow
    var::Id
    type::Term # 1->T or just T ???
end
struct EConc <: Arrow
    ops_dot_ordered::Array{Arrow}
    # Each lambda must RETURN a BOX, but really WE WILL BE EXTREMELY GENEROUS WITH THE TYPECHECKING
end

struct EUnit <: Data end

struct EAbs <: Arrow # A to "1->A"
    body::Data  # u Sure it's not Box?
end
struct EPop <: Data # "1->A" to A
    body::Arrow  # u Sure it's not Box?
end

# Fine, good, now WRITE K([2,3], e2) = 3 PLEASE! :)





# Here you live in the CARTESIAN category:
struct EProd <: Box
    data::Array{Data}
end
struct EProdF <: Box
    data::Array{Arrow}
end

struct ESumTerm <: Data
    data::Box
    tag::Index
    # SEE what's happening?? NO other Data has 2 fields like this!! This because the optional thing here is DATA.
    # It's REALLY an ADDITIONAL LAYER OF ABSTRACTION...
end
struct Ediag <: Box
    data::Data
    n::Index # Is this needed? Or superfluous? Or is it a dependentent type?
    # Very important: NOTE THAT THIS CAN BE 1, AS WELL AS 0 !!!!!!
end
struct Esquash <: Data
    box::Box
    n::Index # Is this needed? Or superfluous? Or is it a dependentent type?
    # Very important: What does it happen when this is 1, and/or 0 ???!!!
end
struct EAnno <: Data # ANNOTATION syntax
    expr::Data
    type::Term # Term ???
end

Base.:(==)(a::EProd, b::EProd) = Base.:(==)(a.data, b.data)



reduc(t::EGlob)::Expr = t
reduc(t::ELoc)::Expr = t
reduc(t::EUnit)::Expr = t
reduc(t::EAbs)::Expr = EAbs(reduc(t.body))
reduc(t::EPop)::Expr = reduc(t.body) # It got popped !!! # Should i NOT reduce it, to pop it ONLY ONCE AT A TIME & allow for Partial ?? >>  <<
reduc(t::EProdF)::Expr = EProd(t.data .|> reduc)
reduc(t::ESumTerm)::Expr = ESumTerm(t.tag, t.data |> reduc)
reduc(t::Ediag)::Expr = t
reduc(t::Esquash)::Expr = t
reduc(t::EAnno)::Expr = EAnno(t.expr |> reduc, t.type)
function reduc(t::EConc)::Expr =
    ops = t.ops_dot_ordered .|> reduc
    result = Array{Expr}([ops[1]])
    cursor = 2
    while cursor < (ops|> length)  # This whole thing should be a foldl, i'm just not great @ it
        op1, op2 = result[end], ops[cursor]
        op1, op2 = (ops[1] isa EAnno ? ops[1].expr : ops[1]), (ops[2] isa EAnno ? ops[2].expr : ops[2])
        if (op2 isa Ediag)
            result[end] = EProdF([op1 for n in op2.n])
        elseif (op2 isa Esquash && op1 isa ESumTerm) # Supposed to be typechecked A+A
            result[end] = op1.data
        elseif ()
            # Y'know, the ACTUAL (ELoc) application goes here ....
        else
            push!(result, op2)
            cursor = cursor + 1
        end
    end
    if length(result) == 1
        return result[1]
    else
        return EConc(result)
    end
end

# pr(x::EGlob)::String = "$(x.var)"
# pr(x::ELoc)::String = "$(x.n)"
# pr(x::EUnit)::String = "T"
# pr(x::EAbs)::String = "/{$(pr(x.body))}"
# pr(x::EPop)::String = "$(pr(x.body))()"
# pr(x::EProdF)::String = "[$(join(x.data .|> pr, ", "))]"
# pr(x::ESumTerm)::String = "$(x.tag)_$(pr(x.data))"
# pr(x::Ediag)::String = "Δ"
# pr(x::Esquash)::String = "∇"
# pr(x::EAnno)::String = "$(pr(x.expr)):$(pr(x.type))"
# function pr(x::EConc)::String
#     x.ops_dot_ordered .|> pr |> x->join(x, ".")
#     # if length(x.ops_dot_ordered) == 2
#     #     arg, func = x.ops_dot_ordered[1], x.ops_dot_ordered[2]
#     #     # arg = (arg isa EProd && length(arg.data)==1) ? (arg.data[1] |> pr) : (arg |> pr)
#     #     arg = (arg isa EProd) ? (arg |> pr)[2:end-1] : (arg |> pr)
#     #     pr(func) * "(" * arg * ")"
#     # elseif length(x.ops_dot_ordered) <= 1
#     #     throw(DomainError("howw $(x)"))
#     # else
#     #     x.ops_dot_ordered .|> pr |> x->join(x, ".")
#     # end
# end

# ############################## Base.getindex(a::A, i::Index) = a.a[i]

# small helper funcs
# # # EAppSwitch(func, args) = EApp([args, func])
# # # EAppAuto(func, args) = EApp([EProd([args]), func])
# # # EGlobAuto(n::Id) = EGlob(n, TGlob(uppercase(n)))

S = EConc([Ediag(3), ])


S = EAbs(EAppAuto(EAppAuto(ELoc(1), ELoc(3)), EAppAuto(ELoc(2), ELoc(3))))
pr(S)

reduc(EAbs(EAppSwitch(S, EProd([EGlobAuto("f"), EGlobAuto("g"), EGlobAuto("x")])))) |> pr

f = EAbs(ELoc(1))
g = EAbs(EGlobAuto("y"))
reduc(EAppSwitch(S, EProd([f, g, EGlobAuto("x")]))) |> pr

# Remember: At this point (not typechecked) it IS possible to be recursive!
ycomb = EAbs(EApp([ELoc(1), ELoc(1)]))
reduc(EApp([ycomb, ycomb])) |> pr
# EVEN IF, note that we ARE amart enough to not go ahead at inf, which is Good!
# I think it's because we are secretly a Fix, ie when EApp|>reduc is same as itself, we STOP


# Sum types 1. : CASE: ( i e ending on a single type C)
f = EAbs(EGlob("cdef", TGlob("C")))
g = EAbs(ELoc(1))

e = ESumTerm(1, EProd([EGlob("cpass", TGlob("C"))]))
case2 = EAbs(EApp([ELoc(1), EBranches([ELoc(2), ELoc(3)])]))  # Case 2 meaning a sum of 2 types

reduc(EApp([EProd([e,f,g]), case2]))

# Sum types 2. : IF: ( i e on 1+1)

Tbool = TSum([TProd([]), TProd([])])
if_ = EAbs(EApp([EAnno(EApp([ELoc(2), ELoc(1)]), Tbool), EBranches([EApp([ELoc(1), ELoc(3)]), EApp([ELoc(1), ELoc(4)])])]))
# What THIS WOULD REQUIRE is, a POP/PartialApp to say that NO, you are Not interested in ^^ what comes out of Tbool, ONLY as a redirection !!
# Well, EITHER that, OR the (A+B)xC --> (AxC)+(BxC) function: i THINK you can use that as well, if you look closely !!
# if_ = EAbs(EApp([
#     EProd([ELoc(1), EAnno(EApp([ELoc(2), ELoc(1)]), Tbool)]),
#     magic_distr_func,
#     magic_remove_dumb_1x_func,
#     EBranches([ELoc(3), ELoc(4)])
# ]))
# infer_type_rec(if_).res_type |> pr

# NOT used by the above:
arity(base::Index, t::EGlob)::Index= base
arity(base::Index, t::ELoc)::Index = max(base, t.n)
arity(base::Index, t::EUnit)::Index = base
arity(base::Index, t::EApp)::Index = t.ops_dot_ordered .|> arity |> maximum
arity(base::Index, t::EAbs)::Index = base # Lam(arity(base, t.body))
arity(base::Index, t::EProd)::Index = t.data .|> (x->arity(base, x)) |> (x->maximum(x, init=0))
arity(base::Index, t::EAnno)::Index = arity(base, t.expr)
arity(base::Index, t::EBranches)::Index = t.ops_chances .|> (x->arity(base, x)) |> maximum
arity(base::Index, t::ESumTerm)::Index = arity(base, t.data)
arity(t::Expr)::Index = arity(0, t)


# Type functions


TFunAuto(tin, tout) = TTerm(tin, tout)
TTermAuto(tin, tout) = TTerm(TProd([tin]), tout)
TAppAuto(tfun, targ) = TApp([TProd([targ]), tfun])


subst(news::Array{Term}, t::TGlob)::Term= t
subst(news::Array{Term}, t::TLocInt)::Term = if t.var <= length(news) news[t.var] else throw(DomainError("Undefined local var $(t.var), n args given = $(length(news))" )) end
subst(news::Array{Term}, t::TTop)::Term = t
subst(news::Array{Term}, t::TTerm)::Term = TTerm(subst(news, t.t_in), subst(news, t.t_out))
subst(news::Array{Term}, t::TAbs)::Term = t # TAbs(subst(news, t.body))
subst(news::Array{Term}, t::TProd)::Term = TProd(t.data .|> (x->subst(news, x)))
subst(news::Array{Term}, t::TSum)::Term = TSum(t.data .|> (x->subst(news, x)))
subst(news::Array{Term}, t::TApp)::Term = TApp(t.ops_dot_ordered .|> x->subst(news, x))
subst(news::Array{Term}, t::TSumTerm)::Term = TSumTerm(t.tag, subst(news, t.data))

reduc(t::TGlob)::Term = t
reduc(t::TLocInt)::Term = t
reduc(t::TTop)::Term = t
reduc(t::TTerm)::Term = TTerm(t.t_in |> reduc, t.t_out |> reduc)
reduc(t::TAbs)::Term = TAbs(reduc(t.body))
reduc(t::TApp)::Term = reduc(t.ops_dot_ordered .|> reduc) # EApp is AN OBJECT THAT REPRESENTS A COMPUTATION (it's only "reduc" here since which one is "typechecked at runtime")
reduc(t::TProd)::Term = TProd(t.data .|> reduc)
reduc(t::TSum)::Term = TSum(t.data .|> reduc)
reduc(t::TSumTerm)::Term = TSumTerm(t.tag, t.data |> reduc)
function reduc(ops::Array{Term})
    #println("> doing the ", typeof(func),  " ", typeof(arg), " thing")
    if ops[1] isa TAbs ops[1] = reduc(Array{Term}([TProd([]), ops[1]])) end # this is because i still havent decided between prods and 0-arg'd lambda's.
    #^ this MIGHT VERY WELL FAIL, idk
    while (length(ops) >= 2 && ops[1] isa TProd && ops[2] isa TAbs) ops = vcat([subst(ops[1].data, ops[2].body) |> reduc], ops[3:end]) end
    # TODO: make this into a more reasonable stack
    return length(ops) >= 2 ? TApp(ops) : ops[1]
end

pr(x::TGlob)::String = "$(x.var)"
pr(x::TLocInt)::String = "T$(x.var)"
pr(x::TTop)::String = "⊥"
# pr(x::TExists)::String = "∃$(x.var)"
pr(x::TAbs)::String = "∀($(x.body |> pr))" #(arity(x.body) > 0) ? ("∀($(x.body |> pr))") : (x.body |> pr)
function pr(x::TProd; is_an_arg::Bool = false)::String
    if is_an_arg
        join(x.data .|> pr, " x ")
    elseif length(x.data) == 0
        is_an_arg ? "" : "1T"
    else
        "[$(join(x.data .|> pr, " x "))]"
    end
end
function pr(x::TTerm)::String
    if x.t_in isa TTerm
        return "(" * (x.t_in |> pr) * ")->" * (x.t_out|> pr )
    elseif (x.t_in isa TProd && x.t_in.data |> length == 1 && x.t_in.data[1] isa TTerm)
        return "(" * (pr(x.t_in; is_an_arg=true)) * ")->" * (x.t_out|> pr )
    elseif (x.t_in isa TProd && x.t_in.data |> length == 1)
        return (pr(x.t_in; is_an_arg=true)) * "->" * (x.t_out|> pr )
    else return (x.t_in |> pr) * "->" *( x.t_out|> pr)
    end
end
function pr(x::TSumTerm)::String
    if x.data isa TProd
        return x.tag * "($(pr(x.data; is_an_arg=true)))"
    else
        return x.tag * "($(x.data |> pr))"
    end
end
pr(x::TSum)::String = "($(join(x.data .|> pr, " + ")))"
# pr(x::TApp)::String = x |>just_pr  # Did i regret this? Yes!
# just_pr(x::TApp) = x.ops_dot_ordered .|> pr .|>(x->"($(x))") |> (x->join(x, " .")) |> (x->"[Ap $(x)]")
function pr(x::TApp)::String
    if length(x.ops_dot_ordered) == 2
        arg, func = x.ops_dot_ordered[1], x.ops_dot_ordered[2]
        # arg = (arg isa TProd && length(arg.data)==1) ? (arg.data[1] |> pr) : (arg |> pr)
        arg = (arg isa TProd) ? (arg |> pr)[2:end-1] : (arg |> pr)
        pr(func) * "(" * arg * ")"
    elseif length(x.ops_dot_ordered) <= 1
        throw(DomainError("howw $(x)"))
    else
        x.ops_dot_ordered .|> pr |> x->join(x, ".") |> (x->"[Ap $(x)]")
    end
end
pr(xs::Array{Term}) = xs .|> pr
just_pr(x::Term) = pr(x)


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
arity(t::Term)::Index = arity(0, t)


EGlob("x", TGlob("A"))
EAnno(ELoc(1), TFunAuto(TGlob("A"), TGlob("B")))
EAnno(ELoc(2), TAbs(TLocInt(1)))

SType1 = TFunAuto(TGlob("X"), TGlob("A"))
SType2 = TFunAuto(TGlob("X"), TFunAuto(TGlob("A"), TGlob("B")))
SType = TFunAuto(TProd([SType2, SType1, TGlob("X")]), TGlob("B"))
SType |> pr

EGlob("S", TFunAuto(TGlob("A"), TGlob("B"))) |> pr
TFunAuto(TGlob("A"), TGlob("B")) |> pr

# Now polymorphicly:
SType1P = TFunAuto(TLocInt(3), TLocInt(2))
SType2P = TFunAuto(TLocInt(3), TFunAuto(TLocInt(2), TLocInt(1)))
STypeP = TAbs(TTerm(TProd([SType2P, SType1P, TLocInt(3)]), TLocInt(1)))
STypeP |> pr



