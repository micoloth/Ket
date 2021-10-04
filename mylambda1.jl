
Index = Int
Id = String
Error = String

abstract type Expr end
abstract type Type_ end

########## Expres




# IDEA: a sum means two possible REFERENCED 1-STATES,
# in the same way a prod means two possible DEREFERENCED 0-STATES.

# If you see a COMPUTATION/Program call as a DEREFERENCING,
# That is,
# sure prods are better, but that's NOT IT:

# a DATA REPRESENTING COMPUTATION  is also CHOSE WHAT THING TO RUN.


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
    # important idea: If you are only wrapping a product you ALREADY HAVE, this makes no sense.
    # If you are introducing your prod via DIAGONAL FUNCTION, instead.. Now we are talking !!!
    data::Array{Expr}
end

# IDEA: you have that: You are wondering:
# If you have to define 2 branches of computation (even if you only do 1),
# WHERE DOES IT END?

# But this is dual to: If you must provide 2 args to make a product, WHERE DO THESE COME FROM???

# Idea: You can "Compile"* a  (a:A) .diag<3> .[f,g,h]   # (Here assuming (AxBxC) .((A>A)x(B>B)x(C>C)) does the right application, not obvious)  # * (apply some parts, associatively, remember)
# Into: (a:A) .{[f.body, g.body, h.body]}  where the TLoc's WORK PROPERLY, and this has this MEANING:

# In the SAME WAY, you now define your [f,g,h]:(A+A+A) .SQUASH:((A+A+A)->A) |--> a:A
# in this PRECOMPILED way: as:(A+A+A) .{[f.body, g.body, h.body]} |--> a:A .

# ^ These are BOTH oversimplifications, even if they DO make these PARTICULAR programs faster to interpret ...


# >>> STILL this is a thing that exists:
# # # ------ > It's ALMOST LIKE, IF DATA WERE PRODUCT-LIKE, COMPUTATION WAS SUM-LIKE,
# BUT,
# You are now using DATA TO REPRESENT COMPUTATION .......... S.........

struct ESumTerm <: Expr
    tag::Index
    data::Expr
    # SEE what's happening?? NO other struct has 2 fields like this!! This because the optional thing here is DATA.
end
struct EBranches <: Expr
    ops_chances::Array{Expr}
    # Each one must compute to a lambda  # ( I mean this is not new..)
    # Also, FINE, i'm giving up & saying these have to TYPECHECK TO A SINGLE OUTPUT
end
struct EAnno <: Expr # ANNOTATION syntax
    expr::Expr
    type::Type_ # Type_ ???
end
Base.:(==)(a::EProd, b::EProd) = Base.:(==)(a.data, b.data)


# Another important thing about sum/prods:
# You COULD ALREADY define your Diagonal Prod:
# EAbs(EProd([ELoc(1), ELoc(1), ELoc(1)])) |> pr
# Of Type: TForall(TTermAuto(TLoc(1), TProd([TLoc(1), TLoc(1), TLoc(1)]))) |> pr

# NOW, you can ALSO define the DUAL thing abou prod, which is (believe it or not):
# EAbs(EBranches())
# TForall(TTermAuto(TProd([TLoc(1), TLoc(1), TLoc(1)]), TLoc(1))) |> pr

########## Types

# Remember: (a+b) x (c+d) == axc + axd + bxc + bxd

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
    t_in::Type_  # Type of input, should be a TProd.
    # NOTE: This^ Only breaks if it is a TGlob, OR a TSum i guess (unless it's a TSum of TProds, that's actually the reduced form?)
    t_out::Type_  # type of the output
end
struct TProd <: Type_
    data::Array{Type_}
end
struct TSum <: Type_
    data::Array{Type_}  # THIS IS A BIG PROBLEM. Thanks i hate it!
end
struct TSumTerm <: Type_
    tag::String  # Here, for TYPES, the tag is a string ( for now)
    data::Type_
    # SEE what's happening?? NO other struct has 2 fields like this!! This because the optional thing here is DATA.
end
Base.:(==)(a::TGlob, b::TGlob) = Base.:(==)(a.var, b.var)
Base.:(==)(a::TLoc, b::TLoc) = Base.:(==)(a.var, b.var)
Base.:(==)(a::TForall, b::TForall) = Base.:(==)(a.body, b.body)
Base.:(==)(a::TApp, b::TApp) = all(a.ops_dot_ordered .== b.ops_dot_ordered)
Base.:(==)(a::TTerm, b::TTerm) = (a.t_in == b.t_in) && (a.t_out == b.t_out)
Base.:(==)(a::TProd, b::TProd) = Base.:(==)(a.data, b.data)
Base.:(==)(a::TSum, b::TSum) = Base.:(==)(a.data, b.data)
Base.:(==)(a::TSumTerm, b::TSumTerm) = (a.data == b.data) && (a.tag == b.tag)


pr(x::EGlob)::String = "$(x.n)"
pr(x::ELoc)::String = "$(x.n)"
pr(x::EUnit)::String = "T"
# pr(x::EApp)::String = "(" * pr(x.arg) * " ." * pr(x.func) *")" # join(x.func .|> pr, ".")
pr(x::EAbs)::String = "/{$(pr(x.body))}"
pr(x::EProd)::String = "[$(join(x.data .|> pr, ", "))]"
pr(x::ESumTerm)::String = "$(x.tag)_$(pr(x.data))"
pr(x::EBranches)::String = "{" * (["$(i)_-->$(e|>pr)" for (i,e) in enumerate(x.ops_chances)] |> (s->join(s, ", "))) * ")"
pr(x::EAnno)::String = "$(pr(x.expr)):$(pr(x.type))"
function pr(x::EApp)::String
    if length(x.ops_dot_ordered) == 2
        arg, func = x.ops_dot_ordered[1], x.ops_dot_ordered[2]
        # arg = (arg isa EProd && length(arg.data)==1) ? (arg.data[1] |> pr) : (arg |> pr)
        arg = (arg isa EProd) ? (arg |> pr)[2:end-1] : (arg |> pr)
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
subst(news::Array{Expr}, t::ESumTerm)::Expr = ESumTerm(t.tag, subst(news, t.data))
subst(news::Array{Expr}, t::EBranches)::Expr = EBranches(t.ops_chances .|> x->subst(news, x)) # Just like EApp, This should have No effect being all EAbs's, but just in case.

reduc(t::EGlob)::Expr = t
reduc(t::ELoc)::Expr = t
reduc(t::EUnit)::Expr = t
reduc(t::EAbs)::Expr = EAbs(reduc(t.body))
reduc(t::EApp)::Expr = (t|>pr|>println; reduc(Array{Expr}(t.ops_dot_ordered .|> reduc))) # EApp is AN OBJECT THAT REPRESENTS A COMPUTATION (it's only "reduc" here since which one is "typechecked at runtime")
reduc(t::EProd)::Expr = EProd(t.data .|> reduc)
reduc(t::EAnno)::Expr = EAnno(t.expr |> reduc, t.type)
reduc(t::EBranches)::Expr = EBranches(t.ops_chances .|> reduc)
reduc(t::ESumTerm)::Expr = ESumTerm(t.tag, t.data |> reduc)
function reduc(ops::Array{Expr})::Expr
    #println("> doing the ", typeof(func),  " ", typeof(arg), " thing")
    # if ops[1] isa EAbs ops[1] = reduc(Array{Expr}([EProd([]), ops[1]])) end # this is because i still havent decided between prods and 0-arg'd lambda's.
    #^ this MIGHT VERY WELL FAIL, idk
    while (length(ops) >= 2)
        ops1, ops2 = (ops[1] isa EAnno ? ops[1].expr : ops[1]), (ops[2] isa EAnno ? ops[2].expr : ops[2])
        if (ops1 isa EProd && ops2 isa EAbs)
            ops = vcat(Array{Expr}([subst(ops1.data, ops2.body) |> reduc]), ops[3:end])
        elseif (ops1 isa ESumTerm && ops2 isa EBranches)
            ops = vcat([EApp([ops1.data, ops2.ops_chances[ops1.tag]]) |> reduc], ops[3:end])
        else break
        end
    end
    # TODO: make this into a more reasonable stack
    # TODO: Make it, you know, ACTUALLY compiled ? If it's even possible?  # --wdyk, maybe it's NOT and this is where the actual recursive-turingcompletey-selflooping-level-y interpreter comes in !!
    # TODO: DEFINITELY possible: Boy this is a mess, tidy upp your PRIMITIVES man !!!
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


subst(news::Array{Type_}, t::TGlob)::Type_= t
subst(news::Array{Type_}, t::TLoc)::Type_ = if t.var <= length(news) news[t.var] else throw(DomainError("Undefined local var $(t.var), n args given = $(length(news))" )) end
subst(news::Array{Type_}, t::TTop)::Type_ = t
subst(news::Array{Type_}, t::TTerm)::Type_ = TTerm(subst(news, t.t_in), subst(news, t.t_out))
subst(news::Array{Type_}, t::TForall)::Type_ = t # TForall(subst(news, t.body))
subst(news::Array{Type_}, t::TProd)::Type_ = TProd(t.data .|> (x->subst(news, x)))
subst(news::Array{Type_}, t::TSum)::Type_ = TSum(t.data .|> (x->subst(news, x)))
subst(news::Array{Type_}, t::TApp)::Type_ = TApp(t.ops_dot_ordered .|> x->subst(news, x))
subst(news::Array{Type_}, t::TSumTerm)::Type_ = TSumTerm(t.tag, subst(news, t.data))

reduc(t::TGlob)::Type_ = t
reduc(t::TLoc)::Type_ = t
reduc(t::TTop)::Type_ = t
reduc(t::TTerm)::Type_ = TTerm(t.t_in |> reduc, t.t_out |> reduc)
reduc(t::TForall)::Type_ = TForall(reduc(t.body))
reduc(t::TApp)::Type_ = reduc(t.ops_dot_ordered .|> reduc) # EApp is AN OBJECT THAT REPRESENTS A COMPUTATION (it's only "reduc" here since which one is "typechecked at runtime")
reduc(t::TProd)::Type_ = TProd(t.data .|> reduc)
reduc(t::TSum)::Type_ = TSum(t.data .|> reduc)
reduc(t::TSumTerm)::Type_ = TSumTerm(t.tag, t.data |> reduc)
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
pr(x::TForall)::String = "∀($(x.body |> pr))" #(arity(x.body) > 0) ? ("∀($(x.body |> pr))") : (x.body |> pr)
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
pr(xs::Array{Type_}) = xs .|> pr
just_pr(x::Type_) = pr(x)


# NOT used by the above:
arity(base::Index, t::TGlob)::Index= base
arity(base::Index, t::TLoc)::Index = max(base, t.var)
arity(base::Index, t::TTop)::Index = base
arity(base::Index, t::TApp)::Index = t.ops_dot_ordered .|> (x->arity(base, x)) |> maximum
arity(base::Index, t::TTerm)::Index = [t.t_in, t.t_out] .|> (x->arity(base, x)) |> maximum
arity(base::Index, t::TForall)::Index = base # Lam(arity(base, t.body))
arity(base::Index, t::TProd)::Index = t.data .|> (x->arity(base, x)) |> (x->maximum(x, init=0))
arity(base::Index, t::TSum)::Index = t.data .|> (x->arity(base, x)) |> (x->maximum(x, init=0))
arity(base::Index, t::TSumTerm)::Index = arity(base, t.data)
arity(t::Type_)::Index = arity(0, t)


EGlob("x", TGlob("A"))
EAnno(ELoc(1), TFunAuto(TGlob("A"), TGlob("B")))
EAnno(ELoc(2), TForall(TLoc(1)))

SType1 = TFunAuto(TGlob("X"), TGlob("A"))
SType2 = TFunAuto(TGlob("X"), TFunAuto(TGlob("A"), TGlob("B")))
SType = TFunAuto(TProd([SType2, SType1, TGlob("X")]), TGlob("B"))
SType |> pr

EGlob("S", TFunAuto(TGlob("A"), TGlob("B"))) |> pr
TFunAuto(TGlob("A"), TGlob("B")) |> pr

# Now polymorphicly:
SType1P = TFunAuto(TLoc(3), TLoc(2))
SType2P = TFunAuto(TLoc(3), TFunAuto(TLoc(2), TLoc(1)))
STypeP = TForall(TTerm(TProd([SType2P, SType1P, TLoc(3)]), TLoc(1)))
STypeP |> pr



