
Index = Int
Id = String
Error = String

abstract type TermTag end

########## Types

# Remember: (a+b) x (c+d) == axc + axd + bxc + bxd

struct TypeUniverseTag <: TermTag end
struct TTopTag <: TermTag end
struct TGlobTag <: TermTag
    var::Id
    type::TermTag # If this is a Type, write TypeUniverse
end
struct TLocTag <: TermTag
    # var::Index # It DOESNT have an index for now- because you DONT know the order!
    var_tag::Id # REPETITION of the var name in the func declaration
end
struct TAbsTag <: TermTag
    body::TermTag # idea: this CAN contain (type level) local variables
    var_tags::Array{Id}
end
struct TAppTag <: TermTag # idk why they woudn't have this
    ops_dot_ordered::Array{TermTag}
    # Each one must compute to a TAbs
    # Each lambda must RETURN a TPROD, but really WE WILL BE EXTREMELY GENEROUS WITH THE "TYPECHECKING"
end
struct TTermTag <: TermTag
    t_in::TermTag  # Type of input, should be a TProd.
    # NOTE: This^ Only breaks if it is a TGlob, OR a TSum i guess (unless it's a TSum of TProds, that's actually the reduced form?)
    t_out::TermTag  # type of the output
    # An INSTANCE of this is a TAbsTag. The tags in t_in::TProd SHOULD MATCH!
end
struct TProdTag <: TermTag
    data::Array{TermTag}
    tags::Array{Id}
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
    # Each one must compute to a lambda/TAbs  # ( I mean this is not new..)
    # Really this is a PROD OF MORPHISMS...
    # Except that, also, FINE, i'm giving up & saying these have to TYPECHECK TO A SINGLE OUTPUT
end
struct TAnnoTag <: TermTag # ANNOTATION syntax
    expr::TermTag
    type::TermTag # If this is a Type, write TypeUniverse
end
Base.:(==)(a::TGlobTag, b::TGlobTag) = Base.:(==)(a.var, b.var)
Base.:(==)(a::TLocTag, b::TLocTag) = (a.var == b.var) && (a.var_tag == b.var_tag)
Base.:(==)(a::TAbsTag, b::TAbsTag) = Base.:(==)(a.body, b.body) && all(a.var_tags .== b.var_tags)
Base.:(==)(a::TAppTag, b::TAppTag) = all(a.ops_dot_ordered .== b.ops_dot_ordered)
Base.:(==)(a::TTermTag, b::TTermTag) = (a.t_in == b.t_in) && (a.t_out == b.t_out)
Base.:(==)(a::TProdTag, b::TProdTag) = all(a.data .== b.data) && all(a.tags .== b.tags)
Base.:(==)(a::TSumTag, b::TSumTag) = Base.:(==)(a.data, b.data) && all(a.tags .== b.tags)
Base.:(==)(a::TSumTermTag, b::TSumTermTag) = (a.data == b.data) && (a.tag == b.tag) && (a.tag_name == b.tag_name)
Base.:(==)(a::TAnnoTag, b::TAnnoTag) = (a.expr == b.expr) && (a.type == b.type)

TSumTag(v::Array{TermTag}) = TSumTag(v, [string(i) for i in 1:length(v)])
TProdTag(v::Array{TermTag}) = TProdTag(v, [string(i) for i in 1:length(v)])
TFunAutoTag(tin, tout) = TTermTag(tin, tout)
TTermAutoTag(tin, tout) = TTermTag(TProdTag([tin]), tout)
TAppAutoTag(tfun, targ) = TAppTag([TProdTag([targ]), tfun])
TAppSwitchTag(func, args) = TAppTag([args, func])
TGlobTag(var::Id) = TGlobTag(var, TypeUniverseTag())
TGlobAutoTag(var::Id) = TGlobTag(var, TGlobTag(uppercase(var)))


detag(t::TGlobTag) = TGlob(t.var, detag(t.type))
detag(t::TLocTag) = TLoc(t.var)
detag(t::TAbsTag) = TAbs(detag(t.body))
detag(t::TAppTag) = TApp(detag.(t.ops_dot_ordered))
detag(t::TTermTag) = TTerm(detag(t.t_in), detag(t.t_out))
detag(t::TProdTag) = TProd(detag.(t.data))
detag(t::TSumTag) = TSum(detag.(t.data))
detag(t::TSumTermTag) = TSumTerm(detag(t.data), t.tag, t.tag_name)
detag(t::TAnnoTag) = TSumTerm(detag(t.expr), detag(t.type))

reduc(t::TermTag) = reduc(detag(t))


trace(s::TGlobTag, topLevel::Bool = true)::String = s.var
trace(s::TTermTag, topLevel::Bool = true)::String = trace(s.t_in, topLevel) * "->" * trace(s.t_out, topLevel)
trace(s::TSumTag, topLevel::Bool = true)::String = if (!topLevel) "aSumType"
	else "(" * join([trace(i, false) for i in s.data], " + ") * ")"
	end
trace(s::TProdTag, topLevel::Bool = true)::String =if (!topLevel) "aProdType"
else "(" * join([trace(i, false) for i in s.data], " x ") * ")"
end
# trace(s::Temp_TypeInt, topLevel::Bool = true)::String = string(s.obj)
