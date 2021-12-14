
Index = Int
Id = String
Error = String

abstract type Term end
abstract type TLoc <: Term end

struct TermwError <: Term
    term::Term
    error::Error
end


########## Types

# Remember: (a+b) x (c+d) == axc + axd + bxc + bxd

struct TypeUniverse <: Term end
struct TTop <: Term end
struct TGlob <: Term
    var::Id
    type::Term # If this is a Type, write TypeUniverse
end
struct TLocInt <: TLoc
    var::Index
end
struct TLocStr <: TLoc
    var::Id # REPETITION of the var name in the func declaration
end
struct TAbs <: Term
    body::Term # idea: this CAN contain (type level) local variables
    var_tags::Array{Id}
end
struct TApp <: Term # idk why they woudn't have this
    ops_dot_ordered::Array{Term}
    # Each one must compute to a TAbs
    # Each lambda must RETURN a TPROD, but really WE WILL BE EXTREMELY GENEROUS WITH THE "TYPECHECKING"
end
struct TTerm <: Term
    t_in::Term  # Type of input, should be a TProd.
    # NOTE: This^ Only breaks if it is a TGlob, OR a TSum i guess (unless it's a TSum of TProds, that's actually the reduced form?)
    t_out::Term  # type of the output
    # An INSTANCE of this is a TAbs. The tags in t_in::TProd SHOULD MATCH!
end
struct TProd <: Term
    data::Array{Term}
    data_tags::Dict{Id, Term}
end
struct TSum <: Term
    data::Array{Term}  # THIS IS A BIG PROBLEM. Thanks i hate it!
    tags::Array{Id}
end
struct TSumTerm <: Term
    tag::Index
    tag_name::Id  # Here, you have ALSO a string ( for now)
    data::Term
    # SEE what's happening?? NO other struct has 2 fields like this!! This because the optional thing here is DATA.
    # The tag_name SHOULD BE ONE IN TSum().tags
end
struct TBranches <: Term
    ops_chances::Array{Term}
    # Each one must compute to a lambda/TAbs  # ( I mean this is not new..)
    # Really this is a PROD OF MORPHISMS...
    # Except that, also, FINE, i'm giving up & saying these have to TYPECHECK TO A SINGLE OUTPUT
    tags::Array{Id} # WHY/HOW are branches supposed to have NAMES..... JESUS what a mess .....
end
struct TAnno <: Term # ANNOTATION syntax
    expr::Term
    type::Term # If this is a Type, write TypeUniverse
end
struct TConc <: Term
    ops_dot_ordered::Array{Term}
end
struct TInt <: Term
    n::Index
end
struct TIntSum <: Term
    ns::Array{Term}
end
struct TIntProd <: Term
    ns::Array{Term}
end
struct TN <: Term end
struct TS <: Term end
struct TStr <: Term
    s::String
end
struct TAppend <: Term
    prods::Array{Term}
end


Base.:(==)(a::TGlob, b::TGlob) = Base.:(==)(a.var, b.var)
Base.:(==)(a::TLocInt, b::TLocInt) = (a.var == b.var) # && (a.var == b.var)
Base.:(==)(a::TLocStr, b::TLocStr) = (a.var == b.var) # && (a.var == b.var)
Base.:(==)(a::TAbs, b::TAbs) = Base.:(==)(a.body, b.body) && all(a.var_tags .== b.var_tags)
Base.:(==)(a::TApp, b::TApp) = all(a.ops_dot_ordered .== b.ops_dot_ordered)
Base.:(==)(a::TConc, b::TConc) = all(a.ops_dot_ordered .== b.ops_dot_ordered)
Base.:(==)(a::TTerm, b::TTerm) = (a.t_in == b.t_in) && (a.t_out == b.t_out)
Base.:(==)(a::TProd, b::TProd) = (length(a.data) == length(b.data)) && all(a.data .== b.data) && (a.data_tags == b.data_tags)
Base.:(==)(a::TSum, b::TSum) = Base.:(==)(a.data, b.data) && all(a.tags .== b.tags)
Base.:(==)(a::TSumTerm, b::TSumTerm) = (a.data == b.data) && (a.tag == b.tag) && (a.tag_name == b.tag_name)
Base.:(==)(a::TAnno, b::TAnno) = (a.expr == b.expr) && (a.type == b.type)
Base.:(==)(a::TInt, b::TInt) = (a.n == b.n)
Base.:(==)(a::TIntSum, b::TIntSum) = all(a.ns .== b.ns)
Base.:(==)(a::TIntProd, b::TIntProd) = all(a.ns .== b.ns)
Base.:(==)(a::TAppend, b::TAppend) = all(a.prods .== b.prods)
Base.:(==)(a::TStr, b::TStr) = (a.s == b.s)

TAbs(body::Term) = TAbs(body, [string(i) for i in 1:arity(body)])
TSum(v::Array{Term}) = TSum(v, [string(i) for i in 1:length(v)])
TProd(v::Array{Term}) = TProd(v, Dict{Id, Term}([]))
TProd(d::Dict{Id, Term}) = TProd(Array{Term}([]), d)
TBranches(v::Array{Term}) = TBranches(v, [string(i) for i in 1:length(v)])
TFunAuto(tin, tout) = TTerm(tin, tout)
TTermAuto(tin, tout) = TTerm(TProd(Array{Term}([tin])), tout)
TAppAuto(tfun, targ) = TApp(Array{Term}([TProd(Array{Term}([targ])), tfun]))
TAppSwitch(func, args) = TApp([args, func])
TTermEmpty(res_type::Term) = TTerm(TProd(Array{Term}([])), res_type)
TGlob(var::Id) = TGlob(var, TypeUniverse())
TGlobAuto(var::Id) = TGlob(var, TGlob(uppercase(var)))
TGlobAutoCtx(var::Id) = TGlob(var, TTermEmpty(TGlob(uppercase(var))))


# detag(t::TGlob) = TGlob(t.var, detag(t.type))
# detag(t::TLocInt) = TLocInt(t.var)
# detag(t::TAbs) = TAbs(detag(t.body))
# detag(t::TApp) = TApp(detag.(t.ops_dot_ordered))
# detag(t::TTerm) = TTerm(detag(t.t_in), detag(t.t_out))
# detag(t::TProd) = TProd(detag.(t.data))
# detag(t::TSum) = TSum(detag.(t.data))
# detag(t::TSumTerm) = TSumTerm(detag(t.data), t.tag, t.tag_name)
# detag(t::TAnno) = TAnno(detag(t.expr), detag(t.type))

# reduc(t::Term) = reduc(detag(t))


# trace(s::TGlob, topLevel::Bool = true)::String = s.var
# trace(s::TTerm, topLevel::Bool = true)::String = trace(s.t_in, topLevel) * "->" * trace(s.t_out, topLevel)
# trace(s::TSum, topLevel::Bool = true)::String = if (!topLevel) "aSumType"
# 	else "(" * join([trace(i, false) for i in s.data], " + ") * ")"
# 	end
# trace(s::TProd, topLevel::Bool = true)::String =if (!topLevel) "aProdType"
# else "(" * join([trace(i, false) for i in s.data], " x ") * ")"
# end
# # trace(s::Temp_TypeInt, topLevel::Bool = true)::String = string(s.obj)



subst(news::TProd, t::TGlob)::Term= t
subst(news::TProd, t::TTop)::Term = t
subst(news::TProd, t::TypeUniverse)::Term = t
subst(news::TProd, t::TN)::Term = t
subst(news::TProd, t::TS)::Term = t
subst(news::TProd, t::TInt)::Term = t
subst(news::TProd, t::TStr)::Term = t
subst(news::TProd, t::TIntSum)::Term = TIntSum(t.ns .|> x->subst(news, x))
subst(news::TProd, t::TIntProd)::Term = TIntProd(t.ns .|> x->subst(news, x))
subst(news::TProd, t::TAppend)::Term = TAppend(t.prods .|> x->subst(news, x))
subst(news::TProd, t::TTerm)::Term = TTerm(subst(news, t.t_in), subst(news, t.t_out))
subst(news::TProd, t::TAbs)::Term = t # TAbs(subst(news, t.body))
subst(news::TProd, t::TProd)::Term = TProd(t.data .|> (x->subst(news, x)), Dict{Id, Term}(k=>subst(news, val) for (k, val) in t.data_tags))
subst(news::TProd, t::TSum)::Term = TSum(t.data .|> (x->subst(news, x)), t.tags)
subst(news::TProd, t::TApp)::Term = TApp(t.ops_dot_ordered .|> x->subst(news, x))
subst(news::TProd, t::TConc)::Term = TConc(t.ops_dot_ordered .|> x->subst(news, x))
subst(news::TProd, t::TSumTerm)::Term = TSumTerm(t.tag, t.tag_name, subst(news, t.data))
subst(news::TProd, t::TAnno)::Term = TAnno(subst(news, t.expr), t.type)
subst(news::TProd, t::TBranches)::Term = TBranches(t.ops_chances .|> x->subst(news, x), t.tags) # Just like TApp, This should have No effect being all TAbs's, but just in case.
subst(news::TProd, t::TLocInt)::Term = if t.var <= length(news.data) news.data[t.var] else throw(DomainError("Undefined local var $(t.var), n args given = $(length(news.data))" )) end
subst(news::TProd, t::TLocStr)::Term = if (t.var in keys(news.data_tags)) news.data_tags[t.var] else throw(DomainError("Undefined local var named $(t.var), n args given = $(news.data_tags)" )) end
subst(news::TProd, t::TermwError)::Term = TermwError(subst(news, t.term), t.error)
# subst(news::Array{Term}, t::TLocInt)::Term = if t.var <= length(news) news[t.var] else throw(DomainError("Undefined local var $(t.var), n args given = $(length(news))" )) end

reduc(t::TGlob)::Term = t
reduc(t::TLocInt)::Term = t
reduc(t::TLocStr)::Term = t
reduc(t::TTop)::Term = t
reduc(t::TypeUniverse)::Term = t
reduc(t::TN)::Term = t
reduc(t::TS)::Term = t
reduc(t::TInt)::Term = t
reduc(t::TStr)::Term = t
reduc(t::TIntSum)::Term = all(t.ns .|> (x->x isa TInt)) ? TInt(sum(t.ns .|> (x->x.n))) : t
reduc(t::TIntProd)::Term = all(t.ns .|> (x->x isa TInt)) ? TInt(prod(t.ns .|> (x->x.n))) : t
reduc(t::TTerm)::Term = TTerm(t.t_in |> reduc, t.t_out |> reduc)
reduc(t::TAbs)::Term = TAbs(reduc(t.body), t.var_tags)
reduc(t::TApp)::Term = reduc(Array{Term}(t.ops_dot_ordered .|> reduc)) # TApp is AN OBJECT THAT REPRESENTS A COMPUTATION (it's only "reduc" here since which one is "typechecked at runtime")
reduc(t::TConc)::Term = reduc(Array{Term}(t.ops_dot_ordered .|> reduc)) # TConc is AN OBJECT THAT REPRESENTS A COMPUTATION (it's only "reduc" here since which one is "typechecked at runtime")
reduc(t::TProd)::Term = TProd(t.data .|> reduc, Dict{Id, Term}(k=>reduc(val) for (k, val) in t.data_tags))
reduc(t::TSum)::Term = TSum(t.data .|> reduc, t.tags)
reduc(t::TSumTerm)::Term = TSumTerm(t.tag, t.tag_name, t.data |> reduc)
reduc(t::TAnno; reduc_type=false)::Term = TAnno(t.expr |> reduc, reduc_type ? (t.type|>reduc) : t.type)
reduc(t::TBranches)::Term = TBranches(t.ops_chances .|> reduc, t.tags)
function reduc(ops::Array{Term})::Term
    #println("> doing the ", typeof(func),  " ", typeof(arg), " thing")
    # if ops[1] isa TAbs ops[1] = reduc(Array{Term}([TProd([]), ops[1]])) end # this is because i still havent decided between prods and 0-arg'd lambda's.
    #^ this MIGHT VERY WELL FAIL, idk
    while (length(ops) >= 2)
        ops1, ops2 = (ops[1] isa TAnno ? ops[1].expr : ops[1]), (ops[2] isa TAnno ? ops[2].expr : ops[2])
        if (ops1 isa TProd && ops2 isa TAbs)
            ops = vcat(Array{Term}([subst(ops1, ops2.body) |> reduc]), ops[3:end])
        elseif (ops1 isa TAbs && ops1.body isa TProd && ops2 isa TAbs)
                ops = vcat(Array{Term}([TAbs(subst(ops1.body, ops2.body)) |> reduc]), ops[3:end])
        elseif (ops1 isa TSumTerm && ops2 isa TBranches)
            branches = Dict{String, Term}(n=>s for (n, s) in zip(ops2.tags, ops2.ops_chances))
            ops = vcat([TApp([ops1.data, branches[ops1.tag_name]]) |> reduc], ops[3:end])
        else break
        end
    end
    # TODO: make this into a more reasonable stack
    # TODO: Make it, you know, ACTUALLY compiled ? If it's even possible?  # --wdyk, maybe it's NOT and this is where the actual recursive-turingcompletey-selflooping-level-y interpreter comes in !!
    # TODO: DEFINITELY possible: Boy this is a mess, tidy upp your PRIMITIVES man !!!
    return length(ops) >= 2 ? TApp(ops) : ops[1]
end
function reduc(t::TAppend)::Term
    if t.prod .|> (x->x isa TProd) |> all
        TProd(vcat(t.prods...))
    elseif t.prod .|> (x->x isa TAnno && x.expr isa TProd) |> all
        TAnno(TProd(vcat((t.prods .|> (x->x.expr))...)), TProd(vcat((t.prods .|> (x->x.type))...)))
        # TAnno(TProd(t.prods.|expr .vcat), TProd(t.prods.|type .vcat))
    end
end
reduc(t::TermwError)::Term = TermwError(reduc(t.term), t.error)

pr_T(x::TGlob)::String = "$(x.var)"
pr_T(x::TLocInt)::String = "T$(x.var)"
pr_T(x::TLocStr)::String = "T$(x.var)"
pr_T(x::TTop)::String = "⊥"
pr_T(x::TypeUniverse)::String = "⊥"
pr_T(x::TN)::String = "ℕ"
pr_T(x::TS)::String = "𝕊"
pr_T(x::TInt)::String = "$(x.n)"
pr_T(x::TStr)::String = "\"$(x.s)\""
pr_T(x::TIntSum)::String = join(x.ns .|> pr_T, "+")
pr_T(x::TIntProd)::String = join(x.ns .|> pr_T, "*")
# pr_T(x::TExists)::String = "∃$(x.var)"
pr_T(x::TAbs)::String = "∀($(x.body |> pr_T))" #(arity(x.body) > 0) ? ("∀($(x.body |> pr_T))") : (x.body |> pr_T)
function pr_T(x::TProd; is_an_arg::Bool = false)::String
    # if is_an_arg
    #     fields = zip(x.tags, x.data .|> pr_T) .|> ((n,t),)->n*":"*t
    #     join(fields, " x ")
    # elseif length(x.data) == 0
    #     is_an_arg ? "" : "[]"
    # else
    #     # fields = zip(x.tags, x.data .|> pr_T) .|> ((n,t),)->n*":"*t
    #     "[$(join(x.data .|> pr_T, " x "))]"
    # end
    data_str = x.data .|> pr_T
    dict_str = ["$(k):$(v|>pr_T)" for (k,v) in x.data_tags]
    "[$(join(vcat(data_str, dict_str), " x "))]"
end
function pr_T(x::TTerm)::String
    if x.t_in isa TTerm
        return "(" * (x.t_in |> pr_T) * ")->" * (x.t_out|> pr_T )
    # elseif (x.t_in isa TProd && x.t_in.data |> length == 1 && x.t_in.data[1] isa TTerm)
    #     return "(" * (pr_T(x.t_in; is_an_arg=true)) * ")->" * (x.t_out|> pr_T )
    # elseif (x.t_in isa TProd && x.t_in.data |> length == 1)
    #     return (pr_T(x.t_in; is_an_arg=true)) * "->" * (x.t_out|> pr_T )
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
function pr_T(x::TConc)::String
    x.ops_dot_ordered .|> pr_T |> x->join(x, ".")
end
function pr_T(x::TAppend)::String
    "append(" * x.prods .|> pr_T |> x->join(x, ", ") * ")"
end

pr_T(xs::Array{Term}) = xs .|> pr_T
pr_T(x::TBranches)::String = "{" * (["$(i)_-->$(e|>pr_T)" for (i,e) in enumerate(x.ops_chances)] |> (s->join(s, ", "))) * ")"
pr_T(x::TAnno)::String = "$(pr_E(x.expr)):$(pr_T(x.type))" # Hellloo...
pr_T(x::TermwError)::String = pr_T(x.term) * " w/ error: " * x.error

pr_E(x::TGlob)::String = "$(x.var)"
pr_E(x::TLocInt)::String = "$(x.var)"
pr_E(x::TLocStr)::String = "$(x.var)"
pr_E(x::TTop)::String = "T"
pr_E(x::TN)::String = "ℕ"
pr_E(x::TS)::String = "𝕊"
pr_E(x::TInt)::String = "$(x.n)"
pr_E(x::TStr)::String = "\"$(x.s)\""
pr_E(x::TIntSum)::String = join(x.ns .|> pr_E, "+")
pr_E(x::TIntProd)::String = join(x.ns .|> pr_E, "*")
# pr_E(x::TApp)::String = "(" * pr_E(x.arg) * " ." * pr_E(x.func) *")" # join(x.func .|> pr_E, ".")
pr_E(x::TAbs)::String = "/{$(pr_E(x.body))}"
pr_E(x::TSumTerm)::String = "$(x.tag_name)_$(pr_E(x.data))"
pr_E(x::TBranches)::String = "{" * (["$(i)_-->$(e|>pr_E)" for (i,e) in enumerate(x.ops_chances)] |> (s->join(s, ", "))) * ")"
pr_E(x::TAnno)::String = "$(pr_E(x.expr)):$(pr_T(x.type))"
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
function pr_E(x::TConc)::String
    x.ops_dot_ordered .|> pr_T |> x->join(x, ".")
end

function pr_E(x::TProd)::String
    data_str = x.data .|> pr_E
    dict_str = ["$(k):$(v|>pr_E)" for (k,v) in x.data_tags]
    "[$(join(vcat(data_str, dict_str), ", "))]"
end
pr_E(x::TermwError)::String = x.error*"("*pr_E(x.term)*")"
function pr_T(x::TAppend)::String
    "append(" * x.prods .|> pr_T |> x->join(x, ", ") * ")"
end

function pr_E(x::TTerm)::String
    if x.t_in isa TTerm
        return "type:" * "(" * (x.t_in |> pr_E) * ")->" * (x.t_out|> pr_E )
    # elseif (x.t_in isa TProd && x.t_in.data |> length == 1 && x.t_in.data[1] isa TTerm)
    #     return "(" * (pr_E(x.t_in; is_an_arg=true)) * ")->" * (x.t_out|> pr_E )
    # elseif (x.t_in isa TProd && x.t_in.data |> length == 1)
    #     return (pr_E(x.t_in; is_an_arg=true)) * "->" * (x.t_out|> pr_E )
    else return "type:" * (x.t_in |> pr_E) * "->" *( x.t_out|> pr_E)
    end
end

pr(x) = pr_T(x)
# pr_ctx(i::TTerm) = "Given [$(join(i.t_in.data .|>pr, ", "))], get $(i.t_out|>pr)"
pr_ctx(i::TTerm) = "Given $(i.t_in |>pr), get $(i.t_out|>pr)"
pr_ctx(i::TermwError) = "ERROR $(t.error) Given $(i.term.t_in |>pr), get $(i.term.t_out|>pr)"


# NOT used by the above:
usedLocsSet(t::TGlob)::Set{String}= Set{String}([])
usedLocsSet(t::TLocInt)::Set{String} = Set{String}([])
usedLocsSet(t::TLocStr)::Set{String} = Set{String}([t.var])
usedLocsSet(t::TTop)::Set{String} = Set{String}([])
usedLocsSet(t::TypeUniverse)::Set{String} = Set{String}([])
usedLocsSet(t::TN)::Set{String} = Set{String}([])
usedLocsSet(t::TS)::Set{String} = Set{String}([])
usedLocsSet(t::TInt)::Set{String} = Set{String}([])
usedLocsSet(t::TStr)::Set{String} = Set{String}([])
usedLocsSet(t::TIntSum)::Set{String} = t.ns .|> usedLocsSet |> (x->union(Set{String}([]), x...))
usedLocsSet(t::TIntProd)::Set{String} = t.ns .|> usedLocsSet |> (x->union(Set{String}([]), x...))
usedLocsSet(t::TAppend)::Set{String} = t.prods .|> usedLocsSet |> (x->union(Set{String}([]), x...))
usedLocsSet(t::TApp)::Set{String} = t.ops_dot_ordered .|> usedLocsSet |> (x->union(Set{String}([]), x...))
usedLocsSet(t::TConc)::Set{String} = t.ops_dot_ordered .|> usedLocsSet |> (x->union(Set{String}([]), x...))
usedLocsSet(t::TTerm)::Set{String} = [t.t_in, t.t_out] .|> usedLocsSet |> (x->union(Set{String}([]), x...))
usedLocsSet(t::TAbs)::Set{String} = Set{String}([]) # Lam(usedLocsSet(base, t.body))
usedLocsSet(t::TProd)::Set{String} = union(Set{String}([]), (t.data .|> usedLocsSet)..., (t.data_tags |> values .|> usedLocsSet)...)
usedLocsSet(t::TSum)::Set{String} = t.data .|> usedLocsSet |> (x->union(Set{String}([]), x...))
usedLocsSet(t::TSumTerm)::Set{String} = usedLocsSet(t.data)
usedLocsSet(t::TAnno)::Set{String} = usedLocsSet(t.expr)
usedLocsSet(t::TBranches)::Set{String} = t.ops_chances .|> usedLocsSet |> (x->union(Set{String}([]), x...))
usedLocsSet(t::TSumTerm)::Set{String} = usedLocsSet(t.data)
usedLocsSet(t::TermwError)::Set{String} = usedLocsSet(t.term)

usedLocs(t::TGlob)::Array{Index} = Array{Index}([])
usedLocs(t::TLocInt)::Array{Index} = Array{Index}([t.var])
usedLocs(t::TLocStr)::Array{Index} = Array{Index}([])
usedLocs(t::TTop)::Array{Index} = Array{Index}([])
usedLocs(t::TypeUniverse)::Array{Index} = Array{Index}([])
usedLocs(t::TN)::Array{Index} = Array{Index}([])
usedLocs(t::TS)::Array{Index} = Array{Index}([])
usedLocs(t::TInt)::Array{Index} = Array{Index}([])
usedLocs(t::TIntSum)::Array{Index} = unique(vcat((t.ns .|> usedLocs)...))
usedLocs(t::TIntProd)::Array{Index} = unique(vcat((t.ns .|> usedLocs)...))
usedLocs(t::TAppend)::Array{Index} = unique(vcat((t.prods .|> usedLocs)...))
usedLocs(t::TApp)::Array{Index} = unique(vcat((t.ops_dot_ordered .|> usedLocs)...))
usedLocs(t::TConc)::Array{Index} = unique(vcat((t.ops_dot_ordered .|> usedLocs)...))
usedLocs(t::TProd)::Array{Index} = unique(vcat((t.data .|> usedLocs)..., (t.data_tags |>values .|> usedLocs)...))
usedLocs(t::TSum)::Array{Index} = unique(vcat((t.data .|> usedLocs)...))
usedLocs(t::TSumTerm)::Array{Index} = t.data |> usedLocs
usedLocs(t::TAbs)::Array{Index} = Array{Index}([])
usedLocs(t::TTerm)::Array{Index} = unique(vcat(t.t_in |> usedLocs, t.t_out |> usedLocs))
usedLocs(t::TermwError)::Array{Index} = usedLocs(t.term)


arity_var(base::Index, t::TGlob)::Index= base
arity_var(base::Index, t::TLocInt)::Index = max(base, t.var)
arity_var(base::Index, t::TLocStr)::Index = base
arity_var(base::Index, t::TTop)::Index = base
arity_var(base::Index, t::TypeUniverse)::Index = base
arity_var(base::Index, t::TN)::Index = base
arity_var(base::Index, t::TS)::Index = base
arity_var(base::Index, t::TInt)::Index = base
arity_var(base::Index, t::TIntSum)::Index = t.ns .|> (x->arity_var(base, x)) |> maximum
arity_var(base::Index, t::TIntProd)::Index = t.ns .|> (x->arity_var(base, x)) |> maximum
arity_var(base::Index, t::TAppend)::Index = t.prods .|> (x->arity_var(base, x)) |> maximum
arity_var(base::Index, t::TApp)::Index = t.ops_dot_ordered .|> (x->arity_var(base, x)) |> maximum
arity_var(base::Index, t::TConc)::Index = t.ops_dot_ordered .|> (x->arity_var(base, x)) |> maximum
arity_var(base::Index, t::TTerm)::Index = [t.t_in, t.t_out] .|> (x->arity_var(base, x)) |> maximum
arity_var(base::Index, t::TAbs)::Index = base # Lam(arity_var(base, t.body))
arity_var(base::Index, t::TProd)::Index = vcat((t.data .|> (x->arity_var(base, x)))..., (t.data_tags |> values .|> (x->arity_var(base, x)))...) |> (x->maximum(x, init=0))
arity_var(base::Index, t::TSum)::Index = t.data .|> (x->arity_var(base, x)) |> (x->maximum(x, init=0))
arity_var(base::Index, t::TSumTerm)::Index = arity_var(base, t.data)
arity_var(base::Index, t::TAnno)::Index = arity_var(base, t.expr)
arity_var(base::Index, t::TBranches)::Index = t.ops_chances .|> (x->arity_var(base, x)) |> maximum
arity_var(base::Index, t::TSumTerm)::Index = arity_var(base, t.data)
arity_var(base::Index, t::TermwError)::Index = arity_var(base, t.term)


arity_var(t::Term)::Index = arity_var(0, t)
# arity_set(t::Term)::Index = usedLocsSet(t) |> length
arity(t::Term)::Index = arity_var(t)  #max(arity_var(0, t), arity_set(t)) ?????????


has_errors(t::TGlob)::Bool= false
has_errors(t::TLocInt)::Bool = false
has_errors(t::TLocStr)::Bool = false
has_errors(t::TTop)::Bool = false
has_errors(t::TypeUniverse)::Bool = false
has_errors(t::TN)::Bool = false
has_errors(t::TS)::Bool = false
has_errors(t::TInt)::Bool = false
has_errors(t::TIntSum)::Bool = t.ns .|> has_errors |> any
has_errors(t::TIntProd)::Bool = t.ns .|> has_errors |> any
has_errors(t::TAppend)::Bool = t.prods .|> has_errors |> any
has_errors(t::TApp)::Bool = t.ops_dot_ordered .|> has_errors |> any
has_errors(t::TConc)::Bool = t.ops_dot_ordered .|> has_errors |> any
has_errors(t::TTerm)::Bool = [t.t_in, t.t_out] .|> has_errors |> any
has_errors(t::TAbs)::Bool = t.body |> has_errors # Lam(has_errors(base, t.body))
has_errors(t::TProd)::Bool = (t.data .|> has_errors |> any) || (t.data_tags |>values .|> has_errors |> any)
has_errors(t::TSum)::Bool = t.data .|> has_errors |> any
has_errors(t::TSumTerm)::Bool = has_errors(t.data)
has_errors(t::TAnno)::Bool = has_errors(t.expr)
has_errors(t::TBranches)::Bool = t.ops_chances .|> has_errors |> any
has_errors(t::TSumTerm)::Bool = has_errors(t.data)
has_errors(t::TermwError)::Bool = true



# TGlob   TGlob
# TLocInt   TLocInt
# TTop   TTop
# TTerm   TTerm
# TAbs   TAbs
# TProd   TProd
# TSum   TSum
# TApp   TApp
# TSumTerm   TSumTerm
# TAnno   TAnno
# TBranches   TBranches
# TFunAuto   TFunAuto
# TTermAuto   TTermAuto
# TAppAuto   TAppAuto
# TAppSwi   TAppSwitch
# TGlobAuto   TGlobAuto
# TAppSwitch   TAppSwitch



S = TAbs(TAppAuto(TAppAuto(TLocInt(1), TLocInt(3)), TAppAuto(TLocInt(2), TLocInt(3))))
pr_E(S)

reduc(TAbs(TAppSwitch(S, TProd(Array{Term}([TGlobAuto("f"), TGlobAuto("g"), TGlobAuto("x")]))))) |> pr_E

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

e = TSumTerm(1, "1", TProd(Array{Term}([TGlob("cpass", TGlob("C"))])))
case2 = TAbs(TApp([TLocInt(1), TBranches(Array{Term}([TLocInt(2), TLocInt(3)]))]))  # Case 2 meaning a sum of 2 types

reduc(TApp([TProd([e,f,g]), case2]))

# Sum types 2. : IF: ( i e on 1+1)

Tbool = TSum(Array{Term}([TProd(Array{Term}([])), TProd(Array{Term}([]))]))
if_ = TAbs(TApp([TAnno(TApp([TLocInt(2), TLocInt(1)]), Tbool), TBranches(Array{Term}([TApp([TLocInt(1), TLocInt(3)]), TApp([TLocInt(1), TLocInt(4)])]))]))
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



# Concat:

f1 = TAbs(TProd(Array{Term}([TLocStr("a"), TGlobAuto("b")])))
f2 = TAbs(TProd(Array{Term}([TLocInt(2), TLocInt(1)])))
f3 = TAbs(TProd(Array{Term}([TLocInt(2), TGlobAuto("c"), TLocInt(1), ])))
reduc(TConc([f1, f2, f3])) |> pr
reduc(TConc([TConc([f1, f2]), f3])) |> pr
reduc(TConc([f1, TConc([f2, f3])])) |> pr

