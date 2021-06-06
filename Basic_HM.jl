  
abstract type Expr end
Index = Int

struct Lambda <: Expr
    body::Expr
end
struct Identifier <: Expr
    name::Index
end

struct Apply <: Expr
    fn::Expr
    arg::Expr
end

struct InferenceError
    #"""Raised if the type inference algorithm cannot infer types successfully"""
    message::String
end

struct ParseError
    #"""Raised if the type environment supplied for is incomplete"""
    message::String
end



# =======================================================#
# Types and type constructors
abstract type Type_ end # i'm NOT SURE what this is...
abstract type TypeOperator <: Type_ end # i'm NOT SURE what this is...
#"""An n-ary type constructor which builds a new type from old"""

struct TypeVariable::Type_
    id::Index
end

struct TTop end

struct Function <: TypeOperator
    #"""A binary type constructor which builds function types"""
    from_type::Type_ 
    to_type::Type_
end
struct Product <: TypeOperator
    #"""A binary type constructor which builds function types"""
    type1::Type_ 
    type2::Type_
end

struct TGlob
    name::String
end

# Basic types are constructed with a nullary type constructor
# Integer = TypeOperator("int", [])  # Basic integer
# Bool = TypeOperator("bool", [])  # Basic bool


# =======================================================#
# Type inference machinery

#="""Computes the type of the expression given by node.
The type of the node is computed in the context of the
supplied type environment env. Data types can be introduced into the
language simply by having a predefined set of identifiers in the initial
environment. environment; this way there is no need to change the syntax or, more
importantly, the type-checking program when extending the language.
Args:
    node: The root of the abstract syntax tree.
    env: The type environment is a mapping of expression identifier names
        to type assignments.
        to type assignments.
    non_generic: A set of non-generic variables, or None
Returns:
    The computed type of the expression.
Raises:
    InferenceError: The type of the expression could not be inferred, for example
        if it is not possible to unify two types such as Integer and Bool
    ParseError: The abstract syntax tree rooted at node could not be parsed
"""=#
function analyse(node::Identifier, env, non_generic::Array{Index})
    return get_type(node.name, env, non_generic)
end
function analyse(node::Apply, env, non_generic::Array{Index})
        fun_type = analyse(node.fn, env, non_generic)
        arg_type = analyse(node.arg, env, non_generic)
        result_type = TypeVariable(length(env+1))  # I'd LIKE to use: TTop() # IT WAS: TypeVariable()
        unify(Function(arg_type, result_type), fun_type) # QUESTION: thing to check: DOES unify() HAVE SIDE EFFECTS on the TypeVariable ???
        return result_type # Answer: Yes.. :(  Other question: is TTop bad and TypeVariable good? If so, HOW???  <-- WHOLE POIT DETECTED
end
function analyse(node::Lambda, env, non_generic::Array{Index})
        arg_type = TypeVariable()
        new_env = env.copy()
        new_env[node.v] = arg_type ############################################################################### NAME TO BRUNJI
        new_non_generic = non_generic.copy()
        new_non_generic.add(arg_type)
        result_type = analyse(node.body, new_env, new_non_generic)
        return Function(arg_type, result_type)
end

function get_type(name::Identifier, env, non_generic)# typesynth identifiers
    if  name.name > length(env)
        throw(DomainError("Undefined local name $(name.name), length context given = $(length(env))"))
    else
        env[name.name]
end
# function get_type(name::EGlob, env, non_generic)# typesynth identifiers
# end

function fresh_(tp::TypeVariable, mappings::Dict{TypeVariable, TypeVariable}, non_generic)::Type_
    if is_generic(tp, non_generic) ############################################################################################ ouch
        get!(mappings, tp, TypeVariable())
    else tp
    end
end
function fresh_(tp::Function, mappings::Dict{TypeVariable, TypeVariable}, non_generic)::Type_ # non_generic is read only
    return Function(
        fresh_(prune(tp.from_type), mappings, non_generic), 
        fresh_(prune(tp.to_type), mappings, non_generic))  # non_generic is read only
end
function fresh_(tp::TGlob, mappings::Dict{TypeVariable, TypeVariable}, non_generic)::Type_
    return tp
end
#="""Makes a copy of a type expression.
The type t is copied. The the generic variables are duplicated and the
non_generic variables are shared.
Args:
    t: A type to be copied.
    non_generic: A set of non-generic TypeVariables
"""=#
function fresh(t, non_generic)
    mappings = Dict{TypeVariable, TypeVariable}()   # A mapping of TypeVariables to TypeVariables
    return fresh_(prune(p), mappings, non_generic)
end


# a = prune(t1)
# b = prune(t2)
#="""Unify the two types t1 and t2.
Makes the types t1 and t2 the same.
Args:
    t1: The first type to be made equivalent
    t2: The second type to be be equivalent
Returns:
    None
Raises:
    InferenceError: Raised if the types cannot be unified.
"""=#
###################################################### CHECK you are always pruning!!!
function unify(a::TypeVariable, b) 
    if a != b
        if occurs_in_type(a, b) return InferenceError("recursive unification") end
        a.instance = b ################################################################## k so WHY cant be TTop, remember me ?????
        # And i mean APART from the fact that this should be ExistsTierGamma[a.id] = b <<<<<<
    end
end
function unify(a, b::TypeVariable) 
    unify(prune(b), prune(a))
end
function unify(a::Function, b::Function) 
    unify(prune(a.from_type), prune(b.from_type))
    unify(prune(a.to_type), prune(b.to_type))
end
function unify(a::Product, b::Product) 
    unify(prune(a.type1), prune(b.type1))
    unify(prune(a.type2), prune(b.type2))
end
# Note: the following is the REMAINING case. you should handle (TGLOB, FUNCTION) how you treat (TypeVariable, FUNCTION)...
function unify(a, b) 
    return InferenceError("Type mismatch: $(a) != $(b)")
end

#="""Prune: Returns the currently defining instance of t.
As a side effect, collapses the list of type instances. The function Prune
is used whenever a type expression has to be inspected: it will always
return a type expression which is either an uninstantiated type variable or
a type operator; i.e. it will skip instantiated variables, and will
actually prune them from expressions to remove long chains of instantiated
variables.

############################################# NOTE: this is what i want the CHAINED (upwards) DEREFERENCE to look like

Args:
t: The type to be pruned
Returns:
An uninstantiated TypeVariable or a TypeOperator
"""=#
function prune(t::TypeVariable)
    if t.instance !== nothing
        t.instance = prune(t.instance)
        return t.instance
    end
    return t
end
function prune(t) t end


function is_generic(v, non_generic)
    # Note: Must be called with v pre-pruned !!
    #="""Checks whether a given variable occurs in a list of non-generic variables
    Note that a variables in such a list may be instantiated to a type term,
    in which case the variables contained in the type term are considered
    non-generic.
    Args:
        v: The TypeVariable to be tested for genericity
        non_generic: A set of non-generic TypeVariables
    Returns:
        True if v is a generic variable, otherwise False
    """=#
    return ! occurs_in(v, non_generic)
end


function occurs_in_type(v, type2)
    #Note: Must be called with v pre-pruned
    pruned_type2 = prune(type2)
    if pruned_type2 == v
        return True
    elseif pruned_type2 isa Function # the only TypeOperator for now
        return occurs_in(v, [pruned_type2.from_type, pruned_type2.to_type])
    else
        return False
    end
end

function occurs_in(t, types)
    return [occurs_in_type(t, t2) for t2 in types] |> any
end




# ==================================================================#
# Examples



var1 = TypeVariable()
var2 = TypeVariable()
pair_type = TypeOperator("*", (var1, var2))

var3 = TypeVariable()

my_env = {"pair": Function(var1, Function(var2, pair_type)),
            "true": Bool,
            "cond": Function(Bool, Function(var3, Function(var3, var3))),
            "zero": Function(Integer, Bool),
            "pred": Function(Integer, Integer),
            "times": Function(Integer, Function(Integer, Integer))}


# factorial
p1 = Lambda(
        Apply(
            Apply(  # cond (zero n) 1
                Apply(Identifier("cond"),  # cond (zero n)
                    Apply(Identifier("zero"), Identifier("n"))),
                Identifier("1")),
            Apply(  # times n
                Apply(Identifier("times"), Identifier("n")),
                Apply(Identifier("factorial"),
                    Apply(Identifier("pred"), Identifier("n")))
            )
        )
        ),  # in
Apply(Identifier("factorial"), Identifier("5"))

# Should fail:
# fn x => (pair(x(3) (x(true)))
Lambda("x",
        Apply(
            Apply(Identifier("pair"),
                    Apply(Identifier("x"), Identifier("3"))),
            Apply(Identifier("x"), Identifier("true")))),

# pair(f(3), f(true))
Apply(
    Apply(Identifier("pair"), Apply(Identifier("f"), Identifier("4"))),
    Apply(Identifier("f"), Identifier("true"))),

# let f = (fn x => x) in ((pair (f 4)) (f true))
Let("f", Lambda("x", Identifier("x")), pair),

# fn f => f f (fail)
Lambda("f", Apply(Identifier("f"), Identifier("f"))),

# let g = fn f => 5 in g g
Let("g",
    Lambda("f", Identifier("5")),
    Apply(Identifier("g"), Identifier("g"))),

# example that demonstrates generic and non-generic variables:
# fn g => let f = fn x => g in pair (f 3, f true)
Lambda("g",
        Let("f",
            Lambda("x", Identifier("g")),
            Apply(
                Apply(Identifier("pair"),
                        Apply(Identifier("f"), Identifier("3"))
                        ),
                Apply(Identifier("f"), Identifier("true"))))),

# Function composition
# fn f (fn g (fn arg (f g arg)))
Lambda("f", Lambda("g", Lambda("arg", Apply(Identifier("g"), Apply(Identifier("f"), Identifier("arg"))))))
