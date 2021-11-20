
Index = Int
Id = String
Error = String

abstract type TermTag end

struct TermTagwError <: TermTag
    term::TermTag
    error::Error
end


########## Types

# Remember: (a+b) x (c+d) == axc + axd + bxc + bxd

struct TypeUniverseTag <: TermTag end
struct TTopTag <: TermTag end
struct TGlobTag <: TermTag
    var::Id
    type::TermTag # If this is a Type, write TypeUniverse
end
struct TLocTag <: TermTag
    var::Index # It DOESNT have an index for now- because you DONT know the order!
end
struct TLocStrTag <: TermTag
    var_tag::Id # REPETITION of the var name in the func declaration
end
struct TAbsTag <: TermTag
    body::TermTag # idea: this CAN contain (type level) local variables
    var_tags::Array{Id}
end
struct TAppTag <: TermTag # idk why they woudn't have this
    ops_dot_ordered::Array{TermTag}
    # Each one must compute to a TAbsTag
    # Each lambda must RETURN a TPROD, but really WE WILL BE EXTREMELY GENEROUS WITH THE "TYPECHECKING"
end
struct TTermTag <: TermTag
    t_in::TermTag  # Type of input, should be a TProdTag.
    # NOTE: This^ Only breaks if it is a TGlobTag, OR a TSumTag i guess (unless it's a TSumTag of TProds, that's actually the reduced form?)
    t_out::TermTag  # type of the output
    # An INSTANCE of this is a TAbsTag. The tags in t_in::TProdTag SHOULD MATCH!
end
struct TProdTag <: TermTag
    data::Array{TermTag}
    data_tags::Dict{Id, TermTag}
end
struct TSumTag <: TermTag
    data::Array{TermTag}  # THIS IS A BIG PROBLEM. Thanks i hate it!
    tags::Array{Id}
end
struct TSumTermTag <: TermTag
    tag::Index
    tag_name::Id  # Here, you have ALSO a string ( for now)
    data::TermTag
    # SEE what's happening?? NO other struct hasTag 2 fields like this!! This because the optional thing here is DATA.
    # The tag_name SHOULD BE ONE IN TSumTag().tags
end
struct TBranchesTag <: TermTag
    ops_chances::Array{TermTag}
    # Each one must compute to a lambda/TAbsTag  # ( I mean this is not new..)
    # Really this is a PROD OF MORPHISMS...
    # Except that, also, FINE, i'm giving up & saying these have to TYPECHECK TO A SINGLE OUTPUT
    tags::Array{Id} # WHY/HOW are branches supposed to have NAMES..... JESUS what a mess .....
end
struct TAnnoTag <: TermTag # ANNOTATION syntax
    expr::TermTag
    type::TermTag # If this is a Type, write TypeUniverse
end

Base.:(==)(a::TGlobTag, b::TGlobTag) = Base.:(==)(a.var, b.var)
Base.:(==)(a::TLocTag, b::TLocTag) = (a.var == b.var) # && (a.var == b.var)
Base.:(==)(a::TLocStrTag, b::TLocStrTag) = (a.var_tag == b.var_tag) # && (a.var == b.var)
Base.:(==)(a::TAbsTag, b::TAbsTag) = Base.:(==)(a.body, b.body) && all(a.var_tags .== b.var_tags)
Base.:(==)(a::TAppTag, b::TAppTag) = all(a.ops_dot_ordered .== b.ops_dot_ordered)
Base.:(==)(a::TTermTag, b::TTermTag) = (a.t_in == b.t_in) && (a.t_out == b.t_out)
Base.:(==)(a::TProdTag, b::TProdTag) = (length(a.data) == length(b.data)) && all(a.data .== b.data) && (a.data_tags == b.data_tags)
Base.:(==)(a::TSumTag, b::TSumTag) = Base.:(==)(a.data, b.data) && all(a.tags .== b.tags)
Base.:(==)(a::TSumTermTag, b::TSumTermTag) = (a.data == b.data) && (a.tag == b.tag) && (a.tag_name == b.tag_name)
Base.:(==)(a::TAnnoTag, b::TAnnoTag) = (a.expr == b.expr) && (a.type == b.type)

TGlobTag(var::Id) = TGlobTag(var, TypeUniverseTag())
TGlobAutoTag(var::Id) = TGlobTag(var, TGlobTag(uppercase(var)))
TAbsTag(body::TermTag) = TAbsTag(body, [string(i) for i in 1:arity(body)])
TSumTag(v::Array{TermTag}) = TSumTag(v, [string(i) for i in 1:length(v)])
TProdTag(v::Array{TermTag}) = TProdTag(v, Dict{Id, TermTag}([]))
TProdTag(d::Dict{Id, TermTag}) = TProdTag(Array{TermTag}([]), d)
TBranchesTag(v::Array{TermTag}) = TBranchesTag(v, [string(i) for i in 1:length(v)])
TFunAutoTag(tin, tout) = TTermTag(tin, tout)
TTermAutoTag(tin, tout) = TTermTag(TProdTag(Array{TermTag}([tin])), tout)
TAppAutoTag(tfun, targ) = TAppTag(Array{TermTag}([TProdTag(Array{TermTag}([targ])), tfun]))
TAppSwitchTag(func, args) = TAppTag([args, func])


# detag(t::TGlobTag) = TGlobTag(t.var, detag(t.type))
# detag(t::TLocTag) = TLocTag(t.var)
# detag(t::TAbsTag) = TAbsTag(detag(t.body))
# detag(t::TAppTag) = TAppTag(detag.(t.ops_dot_ordered))
# detag(t::TTermTag) = TTermTag(detag(t.t_in), detag(t.t_out))
# detag(t::TProdTag) = TProdTag(detag.(t.data))
# detag(t::TSumTag) = TSumTag(detag.(t.data))
# detag(t::TSumTermTag) = TSumTermTag(detag(t.data), t.tag, t.tag_name)
# detag(t::TAnnoTag) = TAnnoTag(detag(t.expr), detag(t.type))

# reduc(t::TermTag) = reduc(detag(t))


trace(s::TGlobTag, topLevel::Bool = true)::String = s.var
trace(s::TTermTag, topLevel::Bool = true)::String = trace(s.t_in, topLevel) * "->" * trace(s.t_out, topLevel)
trace(s::TSumTag, topLevel::Bool = true)::String = if (!topLevel) "aSumType"
	else "(" * join([trace(i, false) for i in s.data], " + ") * ")"
	end
trace(s::TProdTag, topLevel::Bool = true)::String =if (!topLevel) "aProdType"
else "(" * join([trace(i, false) for i in s.data], " x ") * ")"
end
# trace(s::Temp_TypeInt, topLevel::Bool = true)::String = string(s.obj)



subst(news::TProdTag, t::TGlobTag)::TermTag= t
subst(news::TProdTag, t::TTopTag)::TermTag = t
subst(news::TProdTag, t::TTermTag)::TermTag = TTermTag(subst(news, t.t_in), subst(news, t.t_out))
subst(news::TProdTag, t::TAbsTag)::TermTag = t # TAbsTag(subst(news, t.body))
subst(news::TProdTag, t::TProdTag)::TermTag = TProdTag(t.data .|> (x->subst(news, x)), Dict{Id, TermTag}(k=>subst(news, val) for (k, val) in t.data_tags))
subst(news::TProdTag, t::TSumTag)::TermTag = TSumTag(t.data .|> (x->subst(news, x)), t.tags)
subst(news::TProdTag, t::TAppTag)::TermTag = TAppTag(t.ops_dot_ordered .|> x->subst(news, x))
subst(news::TProdTag, t::TSumTermTag)::TermTag = TSumTermTag(t.tag, t.tag_name, subst(news, t.data))
subst(news::TProdTag, t::TAnnoTag)::TermTag = TAnnoTag(subst(news, t.expr), t.type)
subst(news::TProdTag, t::TBranchesTag)::TermTag = TBranchesTag(t.ops_chances .|> x->subst(news, x), t.tags) # Just like TAppTag, This should have No effect being all TAbsTag's, but just in case.
subst(news::TProdTag, t::TLocTag)::TermTag = if t.var <= length(news.data) news.data[t.var] else throw(DomainError("Undefined local var $(t.var), n args given = $(length(news.data))" )) end
subst(news::TProdTag, t::TLocStrTag)::TermTag = if (t.var_tag in keys(news.data_tags)) news.data_tags[t.var_tag] else throw(DomainError("Undefined local var $(t.var), n args given = $(length(news.data_tags))" )) end
subst(news::TProdTag, t::TermTagwError)::TermTag = TermTagwError(subst(news, t.term), t.error)
# subst(news::Array{Term}, t::TLoc)::Term = if t.var <= length(news) news[t.var] else throw(DomainError("Undefined local var $(t.var), n args given = $(length(news))" )) end

reduc(t::TGlobTag)::TermTag = t
reduc(t::TLocTag)::TermTag = t
reduc(t::TTopTag)::TermTag = t
reduc(t::TTermTag)::TermTag = TTermTag(t.t_in |> reduc, t.t_out |> reduc)
reduc(t::TAbsTag)::TermTag = TAbsTag(reduc(t.body), t.var_tags)
reduc(t::TAppTag)::TermTag = reduc(Array{TermTag}(t.ops_dot_ordered .|> reduc)) # TAppTag is AN OBJECT THAT REPRESENTS A COMPUTATION (it's only "reduc" here since which one is "typechecked at runtime")
reduc(t::TProdTag)::TermTag = TProdTag(t.data .|> reduc, Dict{Id, TermTag}(k=>reduc(val) for (k, val) in t.data_tags))
reduc(t::TSumTag)::TermTag = TSumTag(t.data .|> reduc, t.tags)
reduc(t::TSumTermTag)::TermTag = TSumTermTag(t.tag, t.tag_name, t.data |> reduc)
reduc(t::TAnnoTag; reduc_type=false)::TermTag = TAnnoTag(t.expr |> reduc, reduc_type ? (t.type|>reduc) : t.type)
reduc(t::TBranchesTag)::TermTag = TBranchesTag(t.ops_chances .|> reduc, t.tags)
function reduc(ops::Array{TermTag})::TermTag
    #println("> doing the ", typeof(func),  " ", typeof(arg), " thing")
    # if ops[1] isa TAbsTag ops[1] = reduc(Array{TermTag}([TProdTag([]), ops[1]])) end # this is because i still havent decided between prods and 0-arg'd lambda's.
    #^ this MIGHT VERY WELL FAIL, idk
    while (length(ops) >= 2)
        ops1, ops2 = (ops[1] isa TAnnoTag ? ops[1].expr : ops[1]), (ops[2] isa TAnnoTag ? ops[2].expr : ops[2])
        if (ops1 isa TProdTag && ops2 isa TAbsTag)
            ops = vcat(Array{TermTag}([subst(ops1, ops2.body) |> reduc]), ops[3:end])
        elseif (ops1 isa TSumTermTag && ops2 isa TBranchesTag)
            branches = Dict{String, TermTag}(n=>s for (n, s) in zip(ops2.tags, ops2.ops_chances))
            ops = vcat([TAppTag([ops1.data, branches[ops1.tag_name]]) |> reduc], ops[3:end])
        else break
        end
    end
    # TODO: make this into a more reasonable stack
    # TODO: Make it, you know, ACTUALLY compiled ? If it's even possible?  # --wdyk, maybe it's NOT and this is where the actual recursive-turingcompletey-selflooping-level-y interpreter comes in !!
    # TODO: DEFINITELY possible: Boy this is a mess, tidy upp your PRIMITIVES man !!!
    return length(ops) >= 2 ? TAppTag(ops) : ops[1]
end
reduc(t::TermTagwError)::TermTag = TermTagwError(reduc(t.term), t.error)


pr_T(x::TGlobTag)::String = "$(x.var)"
pr_T(x::TLocTag)::String = "T$(x.var)"
pr_T(x::TLocStrTag)::String = "T$(x.var_tag)"
pr_T(x::TTopTag)::String = "⊥"
# pr_T(x::TExists)::String = "∃$(x.var)"
pr_T(x::TAbsTag)::String = "∀($(x.body |> pr_T))" #(arity(x.body) > 0) ? ("∀($(x.body |> pr_T))") : (x.body |> pr_T)
function pr_T(x::TProdTag; is_an_arg::Bool = false)::String
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
function pr_T(x::TTermTag)::String
    if x.t_in isa TTermTag
        return "(" * (x.t_in |> pr_T) * ")->" * (x.t_out|> pr_T )
    elseif (x.t_in isa TProdTag && x.t_in.data |> length == 1 && x.t_in.data[1] isa TTermTag)
        return "(" * (pr_T(x.t_in; is_an_arg=true)) * ")->" * (x.t_out|> pr_T )
    elseif (x.t_in isa TProdTag && x.t_in.data |> length == 1)
        return (pr_T(x.t_in; is_an_arg=true)) * "->" * (x.t_out|> pr_T )
    else return (x.t_in |> pr_T) * "->" *( x.t_out|> pr_T)
    end
end
function pr_T(x::TSumTermTag)::String
    if x.data isa TProdTag
        return x.tag_name * "($(pr_T(x.data; is_an_arg=true)))"
    else
        return x.tag_name * "($(x.data |> pr_T))"
    end
end
pr_T(x::TSumTag)::String = "($(join(x.data .|> pr_T, " + ")))"
function pr_T(x::TAppTag)::String
    if length(x.ops_dot_ordered) == 2
        arg, func = x.ops_dot_ordered[1], x.ops_dot_ordered[2]
        # arg = (arg isa TProdTag && length(arg.data)==1) ? (arg.data[1] |> pr_T) : (arg |> pr_T)
        arg = (arg isa TProdTag) ? (arg |> pr_T)[2:end-1] : (arg |> pr_T)
        pr_T(func) * "(" * arg * ")"
    elseif length(x.ops_dot_ordered) <= 1
        throw(DomainError("howw $(x)"))
    else
        x.ops_dot_ordered .|> pr_T |> x->join(x, ".") |> (x->"[Ap $(x)]")
    end
end
pr_T(xs::Array{TermTag}) = xs .|> pr_T
pr_T(x::TBranchesTag)::String = "{" * (["$(i)_-->$(e|>pr_T)" for (i,e) in enumerate(x.ops_chances)] |> (s->join(s, ", "))) * ")"
pr_T(x::TAnnoTag)::String = "$(pr_E(x.expr)):$(pr_T(x.type))" # Hellloo...
pr_T(x::TermTagwError)::String = pr_T(x.term) * " w/ error: " * x.error

pr_E(x::TGlobTag)::String = "$(x.var)"
pr_E(x::TLocTag)::String = "$(x.var)"
pr_E(x::TLocStrTag)::String = "$(x.var_tag)"
pr_E(x::TTopTag)::String = "T"
# pr_E(x::TAppTag)::String = "(" * pr_E(x.arg) * " ." * pr_E(x.func) *")" # join(x.func .|> pr_E, ".")
pr_E(x::TAbsTag)::String = "/{$(pr_E(x.body))}"
pr_E(x::TSumTermTag)::String = "$(x.tag_name)_$(pr_E(x.data))"
pr_E(x::TBranchesTag)::String = "{" * (["$(i)_-->$(e|>pr_E)" for (i,e) in enumerate(x.ops_chances)] |> (s->join(s, ", "))) * ")"
pr_E(x::TAnnoTag)::String = "$(pr_E(x.expr)):$(pr_T(x.type))"
function pr_E(x::TAppTag)::String
    if length(x.ops_dot_ordered) == 2
        arg, func = x.ops_dot_ordered[1], x.ops_dot_ordered[2]
        # arg = (arg isa TProdTag && length(arg.data)==1) ? (arg.data[1] |> pr_E) : (arg |> pr_E)
        arg = (arg isa TProdTag) ? (arg |> pr_E)[2:end-1] : (arg |> pr_E)
        pr_E(func) * "(" * arg * ")"
    elseif length(x.ops_dot_ordered) <= 1
        throw(DomainError("howw $(x)"))
    else
        x.ops_dot_ordered .|> pr_E |> x->join(x, ".")
    end
end
function pr_E(x::TProdTag)::String
    data_str = x.data .|> pr_T
    dict_str = ["$(k):$(v|>pr_T)" for (k,v) in x.data_tags]
    "[$(join(vcat(data_str, dict_str), ", "))]"
end
pr_E(x::TermTagwError)::String = x.error*"("*pr_E(x.term)*")"


pr(x) = pr_T(x)
pr_ctx(i::TTermTag) = "Given [$(join(i.t_in.data .|>pr, ", "))], get $(i.t_out|>pr)"


# NOT used by the above:
usedLocsSet(t::TGlobTag)::Set{String}= Set{String}([])
usedLocsSet(t::TLocTag)::Set{String} = Set{String}([])
usedLocsSet(t::TLocStrTag)::Set{String} = Set{String}([t.var_tag])
usedLocsSet(t::TTopTag)::Set{String} = Set{String}([])
usedLocsSet(t::TAppTag)::Set{String} = t.ops_dot_ordered .|> usedLocsSet |> (x->union(Set{String}([]), x...))
usedLocsSet(t::TTermTag)::Set{String} = [t.t_in, t.t_out] .|> usedLocsSet |> (x->union(Set{String}([]), x...))
usedLocsSet(t::TAbsTag)::Set{String} = Set{String}([]) # Lam(usedLocsSet(base, t.body))
usedLocsSet(t::TProdTag)::Set{String} = union(Set{String}([]), (t.data .|> usedLocsSet)..., (t.data_tags |> values .|> usedLocsSet)...)
usedLocsSet(t::TSumTag)::Set{String} = t.data .|> usedLocsSet |> (x->union(Set{String}([]), x...))
usedLocsSet(t::TSumTermTag)::Set{String} = usedLocsSet(t.data)
usedLocsSet(t::TAnnoTag)::Set{String} = usedLocsSet(t.expr)
usedLocsSet(t::TBranchesTag)::Set{String} = t.ops_chances .|> usedLocsSet |> (x->union(Set{String}([]), x...))
usedLocsSet(t::TSumTermTag)::Set{String} = usedLocsSet(t.data)
usedLocsSet(t::TermTagwError)::Set{String} = usedLocsSet(t.term)

usedLocs(t::TGlobTag)::Array{Index} = Array{Index}([])
usedLocs(t::TLocTag)::Array{Index} = Array{Index}([t.var])
usedLocs(t::TLocStrTag)::Array{Index} = Array{Index}([])
usedLocs(t::TTopTag)::Array{Index} = Array{Index}([])
usedLocs(t::TAppTag)::Array{Index} = unique(vcat((t.ops_dot_ordered .|> usedLocs)...))
usedLocs(t::TProdTag)::Array{Index} = unique(vcat((t.data .|> usedLocs)..., (t.data_tags |>values .|> usedLocs)...))
usedLocs(t::TSumTag)::Array{Index} = unique(vcat((t.data .|> usedLocs)...))
usedLocs(t::TSumTermTag)::Array{Index} = t.data |> usedLocs
usedLocs(t::TAbsTag)::Array{Index} = Array{Index}([])
usedLocs(t::TTermTag)::Array{Index} = unique(vcat(t.t_in |> usedLocs, t.t_out |> usedLocs))
usedLocs(t::TermTagwError)::Array{Index} = usedLocs(t.term)


arity_var(base::Index, t::TGlobTag)::Index= base
arity_var(base::Index, t::TLocTag)::Index = max(base, t.var)
arity_var(base::Index, t::TLocStrTag)::Index = base
arity_var(base::Index, t::TTopTag)::Index = base
arity_var(base::Index, t::TAppTag)::Index = t.ops_dot_ordered .|> (x->arity_var(base, x)) |> maximum
arity_var(base::Index, t::TTermTag)::Index = [t.t_in, t.t_out] .|> (x->arity_var(base, x)) |> maximum
arity_var(base::Index, t::TAbsTag)::Index = base # Lam(arity_var(base, t.body))
arity_var(base::Index, t::TProdTag)::Index = vcat((t.data .|> (x->arity_var(base, x)))..., (t.data_tags |> values .|> (x->arity_var(base, x)))...) |> (x->maximum(x, init=0))
arity_var(base::Index, t::TSumTag)::Index = t.data .|> (x->arity_var(base, x)) |> (x->maximum(x, init=0))
arity_var(base::Index, t::TSumTermTag)::Index = arity_var(base, t.data)
arity_var(base::Index, t::TAnnoTag)::Index = arity_var(base, t.expr)
arity_var(base::Index, t::TBranchesTag)::Index = t.ops_chances .|> (x->arity_var(base, x)) |> maximum
arity_var(base::Index, t::TSumTermTag)::Index = arity_var(base, t.data)
arity_var(base::Index, t::TermTagwError)::Index = arity_var(base, t.term)


arity_var(t::TermTag)::Index = arity_var(0, t)
# arity_set(t::TermTag)::Index = usedLocsSet(t) |> length
arity(t::TermTag)::Index = arity_var(t)  #max(arity_var(0, t), arity_set(t)) ?????????


has_errors(t::TGlobTag)::Bool= false
has_errors(t::TLocTag)::Bool = false
has_errors(t::TLocStrTag)::Bool = false
has_errors(t::TTopTag)::Bool = false
has_errors(t::TAppTag)::Bool = t.ops_dot_ordered .|> has_errors |> any
has_errors(t::TTermTag)::Bool = [t.t_in, t.t_out] .|> has_errors |> any
has_errors(t::TAbsTag)::Bool = t.body |> has_errors # Lam(has_errors(base, t.body))
has_errors(t::TProdTag)::Bool = (t.data .|> has_errors |> any) || (t.data_tags |>values .|> has_errors |> any)
has_errors(t::TSumTag)::Bool = t.data .|> has_errors |> any
has_errors(t::TSumTermTag)::Bool = has_errors(t.data)
has_errors(t::TAnnoTag)::Bool = has_errors(t.expr)
has_errors(t::TBranchesTag)::Bool = t.ops_chances .|> has_errors |> any
has_errors(t::TSumTermTag)::Bool = has_errors(t.data)
has_errors(t::TermTagwError)::Bool = true



# TGlob   TGlobTag
# TLoc   TLocTag
# TTop   TTopTag
# TTerm   TTermTag
# TAbs   TAbsTag
# TProd   TProdTag
# TSum   TSumTag
# TApp   TAppTag
# TSumTerm   TSumTermTag
# TAnno   TAnnoTag
# TBranches   TBranchesTag
# TFunAuto   TFunAutoTag
# TTermAuto   TTermAutoTag
# TAppAuto   TAppAutoTag
# TAppSwi   TAppSwitchTag
# TGlobAuto   TGlobAutoTag
# TAppSwitch   TAppSwitchTag



S = TAbsTag(TAppAutoTag(TAppAutoTag(TLocTag(1), TLocTag(3)), TAppAutoTag(TLocTag(2), TLocTag(3))))
pr_E(S)

reduc(TAbsTag(TAppSwitchTag(S, TProdTag(Array{TermTag}([TGlobAutoTag("f"), TGlobAutoTag("g"), TGlobAutoTag("x")]))))) |> pr_E

f = TAbsTag(TLocTag(1))
g = TAbsTag(TGlobAutoTag("y"))
reduc(TAppSwitchTag(S, TProdTag([f, g, TGlobAutoTag("x")]))) |> pr

# Remember: At this point (not typechecked) it IS possible to be recursive!
ycomb = TAbsTag(TAppTag([TLocTag(1), TLocTag(1)]))
reduc(TAppTag([ycomb, ycomb])) |> pr

# EVEN IF, note that we ARE amart enough to not go ahead at inf, which is Good!
# I think it's because we are secretly a Fix, ie when TAppTag|>reduc is same as itself, we STOP


# Sum types 1. : CASE: ( i e ending on a single type C)
f = TAbsTag(TGlobTag("cdef", TGlobTag("C")))
g = TAbsTag(TLocTag(1))

e = TSumTermTag(1, "1", TProdTag(Array{TermTag}([TGlobTag("cpass", TGlobTag("C"))])))
case2 = TAbsTag(TAppTag([TLocTag(1), TBranchesTag(Array{TermTag}([TLocTag(2), TLocTag(3)]))]))  # Case 2 meaning a sum of 2 types

reduc(TAppTag([TProdTag([e,f,g]), case2]))

# Sum types 2. : IF: ( i e on 1+1)

Tbool = TSumTag(Array{TermTag}([TProdTag(Array{TermTag}([])), TProdTag(Array{TermTag}([]))]))
if_ = TAbsTag(TAppTag([TAnnoTag(TAppTag([TLocTag(2), TLocTag(1)]), Tbool), TBranchesTag(Array{TermTag}([TAppTag([TLocTag(1), TLocTag(3)]), TAppTag([TLocTag(1), TLocTag(4)])]))]))
# What THIS WOULD REQUIRE is, a POP/PartialApp to say that NO, you are Not interested in ^^ what comes out of Tbool, ONLY as a redirection !!
# Well, EITHER that, OR the (A+B)xC --> (AxC)+(BxC) function: i THINK you can use that as well, if you look closely !!
# if_ = TAbsTag(TAppTag([
#     TProdTag([TLocTag(1), TAnnoTag(TAppTag([TLocTag(2), TLocTag(1)]), Tbool)]),
#     magic_distr_func,
#     magic_remove_dumb_1x_func,
#     TBranchesTag([TLocTag(3), TLocTag(4)])
# ]))
# infer_type_rec(if_).res_type |> pr


TGlobTag("x", TGlobTag("A"))
TAnnoTag(TLocTag(1), TFunAutoTag(TGlobTag("A"), TGlobTag("B")))
TAnnoTag(TLocTag(2), TAbsTag(TLocTag(1)))

SType1 = TFunAutoTag(TGlobTag("X"), TGlobTag("A"))
SType2 = TFunAutoTag(TGlobTag("X"), TFunAutoTag(TGlobTag("A"), TGlobTag("B")))
SType = TFunAutoTag(TProdTag([SType2, SType1, TGlobTag("X")]), TGlobTag("B"))
SType |> pr

TGlobTag("S", TFunAutoTag(TGlobTag("A"), TGlobTag("B"))) |> pr
TFunAutoTag(TGlobTag("A"), TGlobTag("B")) |> pr

# Now polymorphicly:
SType1P = TFunAutoTag(TLocTag(3), TLocTag(2))
SType2P = TFunAutoTag(TLocTag(3), TFunAutoTag(TLocTag(2), TLocTag(1)))
STypeP = TAbsTag(TTermTag(TProdTag([SType2P, SType1P, TLocTag(3)]), TLocTag(1)))
STypeP |> pr



