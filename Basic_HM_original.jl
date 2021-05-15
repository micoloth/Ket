  
abstract type Expr end
Index = Int

struct Lambda <: Expr
    v::String
    body::Expr
end
struct Identifier <: Expr
    name::String
end
struct Apply <: Expr
    fn::Expr
    arg::Expr
end
struct Let <: Expr
    v::String
    defn::Expr
    body::Expr
end
struct Letrec <: Expr
    v::String
    defn::Expr
    body::Expr
end

# Exception types
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
# abstract type TypeOperator <: Type_ end # i'm NOT SURE what this is...
#"""An n-ary type constructor which builds a new type from old"""

TOPFREE=100
newvar() = (global TOPFREE = TOPFREE + 1; TOPFREE)


mutable struct TypeVariable<:Type_
    id::Index
    instance::Union{Nothing, Type_}
    name::String
end

TypeVariable() = (v = newvar(); TypeVariable(v, nothing, string(v)))

struct TypeOperator<:Type_
    name::String
    types::Array{Type_}
end

Function(from_type, to_type)::TypeOperator = TypeOperator("->", [from_type, to_type])
Integer_() = TypeOperator("int", [])  # Basic integer
Bool_() = TypeOperator("bool", [])  # Basic bool

pr(t::TypeVariable)::String = t.instance===nothing ? "T"*t.name : "T"*t.name*":"*(t.instance |> pr)
pr(t::TypeOperator)::String = isempty(t.types) ? t.name : "($(join(t.types .|> pr, t.name)))"

# =======================================================#
# Type inference machinery

# """Computes the type of the expression given by node.
# The type of the node is computed in the context of the
# supplied type environment env. Data types can be introduced into the
# language simply by having a predefined set of identifiers in the initial
# environment. environment; this way there is no need to change the syntax or, more
# importantly, the type-checking program when extending the language.
# Args:
#     node: The root of the abstract syntax tree.
#     env: The type environment is a mapping of expression identifier names
#         to type assignments.
#         to type assignments.
#     non_generic: A set of non-generic variables, or None
# Returns:
#     The computed type of the expression.
# Raises:
#     InferenceError: The type of the expression could not be inferred, for example
#         if it is not possible to unify two types such as Integer_ and Bool_
#     ParseError: The abstract syntax tree rooted at node could not be parsed
# """


function analyse(node::Identifier, env, non_generic::Array{Type_}=Array{Type_}([]))
    return get_type(node.name, env, non_generic)
end
function analyse(node::Apply, env, non_generic::Array{Type_}=Array{Type_}([]))
    # println("env: ", [k*":"*pr(v) for (k, v) in env])
    # println("non_generic: ", non_generic .|> pr)
    fun_type = analyse(node.fn, env, non_generic)
    arg_type = analyse(node.arg, env, non_generic)
    result_type = TypeVariable()
    unify(Function(arg_type, result_type), fun_type)
    return result_type
end
function analyse(node::Lambda, env, non_generic::Array{Type_}=Array{Type_}([]))
    # println("env: ", [k*":"*pr(v) for (k, v) in env])
    # println("non_generic: ", non_generic .|> pr)
    arg_type = TypeVariable()
    new_env = copy(env)
    new_env[node.v] = arg_type
    new_non_generic = copy(non_generic)
    push!(new_non_generic, arg_type)
    result_type = analyse(node.body, new_env, new_non_generic)
    return Function(arg_type, result_type)
end
function analyse(node::Let, env, non_generic::Array{Type_}=Array{Type_}([]))
    # println("env: ", [k*":"*pr(v) for (k, v) in env])
    # println("non_generic: ", non_generic .|> pr)
    defn_type = analyse(node.defn, env, non_generic)
    new_env = copy(env)
    new_env[node.v] = defn_type
    return analyse(node.body, new_env, non_generic)
end
function analyse(node::Letrec, env, non_generic::Array{Type_}=Array{Type_}([]))
    # println("env: ", [k*":"*pr(v) for (k, v) in env])
    # println("non_generic: ", non_generic .|> pr)
    new_type = TypeVariable()
    new_env = copy(env)
    new_env[node.v] = new_type
    new_non_generic = copy(non_generic)
    push!(new_non_generic, new_type)
    defn_type = analyse(node.defn, new_env, new_non_generic)
    unify(new_type, defn_type)
    return analyse(node.body, new_env, non_generic)
end


################# 

function get_type(name, env, non_generic)
    # """Get the type of identifier name from the type environment env.
    if name in keys(env)
        return fresh(env[name], non_generic)
    elseif is_integer_literal(name)
        return Integer_()
    else
        throw(ParseError("Undefined symbol $(name)"))
    end
end



function fresh(t, non_generic)
    # Makes a copy of a type expression.
    # The type t is copied. The the generic variables are duplicated and the
    # non_generic variables are shared.
    mappings = Dict{TypeVariable, TypeVariable}()  # A mapping of TypeVariables to TypeVariables
    
    function freshrec(tp)
        p = prune(tp)
        if p isa TypeVariable
            if is_generic(p, non_generic)
                get!(mappings, p, TypeVariable()) 
                #The the generic variables are duplicated, the old->new map is stored in Mappings so that same olds have same news.  Mappings is != from env !!!!!!
            else
                p
            end
        elseif p isa TypeOperator
            return TypeOperator(p.name, [freshrec(x) for x in p.types])
        end
    end
    
    freshrec(t)
end


# Unify the two types t1 and t2.
# Makes the types t1 and t2 the same.
# a = prune(t1)
# b = prune(t2)

function unify(a::TypeVariable, b)
    if a != b
        if occurs_in_type(a, b)
            throw(InferenceError("recursive unification"))
        end
        a.instance = b
    end
end
function unify(a::TypeOperator, b::TypeVariable) 
    unify(prune(b), prune(a))
end
function unify(a::TypeOperator, b::TypeOperator) 
    if (a.name != b.name) || (length(a.types) != length(b.types))
        throw(InferenceError("Type mismatch: $(a) != $(b)"))
    end
    for (p, q) in zip(a.types, b.types)
        unify(prune(p), prune(q))
    end
end
function unify(a, b) 
    throw(DomainError("There are other cases?? ($(a), $(b))"))
end

# """Returns the currently defining instance of t.
# As a side effect, collapses the list of type instances. The function Prune
# is used whenever a type expression has to be inspected: it will always
# return a type expression which is either an uninstantiated type variable or
# a type operator; i.e. it will skip instantiated variables, and will
# actually prune them from expressions to remove long chains of instantiated
# variables.
function prune(t::Type_)
    if ((t isa TypeVariable) && (t.instance !== nothing))
        t.instance = prune(t.instance)
        return t.instance
    end
    return t
end

# """Checks whether a given variable occurs in a list of non-generic variables.
# This means: that a given variable is used somewhere AS A FINAL VALUE (is an instance) , INSTEAD OF AS A variable
# (actually, it can ONLY be a FINAL value if it is NOT a TypeVariable.. So, IT CHECKS IF IT HAS EVER BEEN INSTANTIATED ?)

# [[recursively in nested contexts]]
# Note: Must be called with v pre-pruned

function is_generic(v, non_generic)
    return ! occurs_in(v, non_generic)
end

function occurs_in_type(v, type2)
    # """Checks whether a type variable occurs in a type expression.
    # Note: Must be called with v pre-pruned
    pruned_type2 = prune(type2)
    if pruned_type2 == v
        return true
    elseif pruned_type2 isa TypeOperator
        return occurs_in(v, pruned_type2.types)
    end
    return false
end

function occurs_in(t, types)
    return [occurs_in_type(t, t2) for t2 in types] |> any
end

function is_integer_literal(name)
    return tryparse(Int, name) !== nothing
end


# ==================================================================#
# Example code to exercise the above


function try_exp(env, node)
    try
        t = analyse(node, env)
        println(t)
    catch e
        print(e)
    end
end


var1 = TypeVariable()
var2 = TypeVariable()
pair_type = TypeOperator("*", [var1, var2])

var3 = TypeVariable()

my_env = Dict{String, Type_}("pair"=> Function(var1, Function(var2, pair_type)),
            "true"=> Bool_(),
            "cond"=> Function(Bool_(), Function(var3, Function(var3, var3))),
            "zero"=> Function(Integer_(), Bool_()),
            "pred"=> Function(Integer_(), Integer_()),
            "times"=> Function(Integer_(), Function(Integer_(), Integer_())))

pair = Apply(Apply(Identifier("pair"),
                    Apply(Identifier("f"),
                            Identifier("4"))),
                Apply(Identifier("f"),
                    Identifier("true")))

# factorial
e = Letrec("factorial",  # letrec factorial =
        Lambda("n",  # fn n =>
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
        )
analyse(e, my_env) |> pr

# fn x => (pair(x(3) (x(5)))
TOPFREE=0
e = Lambda("x",
        Apply(
            Apply(Identifier("pair"),
                    Apply(Identifier("x"), Identifier("3"))),
            Apply(Identifier("x"), Identifier("5"))))
analyse(e, my_env) |> pr == "(T1:(int->T6:T2)->T9:(T2*T3:T2))"

# fn x => (pair((y=>pair(y y))(3) (x(5)))
TOPFREE=0
e = Lambda("x",
        Apply(
            Apply(Identifier("pair"),
                    Apply(Lambda("y", Apply(Apply(Identifier("pair"), Identifier("y")), Identifier("y"))), Identifier("3"))),
            Apply(Identifier("x"), Identifier("5"))))
analyse(e, my_env) |> pr == "(T1:(int->T15)->T16:(T2:(T7:int*T8:int)*T3:T15))"

# fn x => (pair((y=>pair(y y))(x(3)) (x(5)))
TOPFREE=0
e = Lambda("x",
        Apply(
            Apply(Identifier("pair"),
                    Apply(Lambda("y", Apply(Apply(Identifier("pair"), Identifier("y")), Identifier("y"))), Apply(Identifier("x"), Identifier("3")))),
            Apply(Identifier("x"), Identifier("5"))))
analyse(e, my_env) |> pr == "(T1:(int->T13:T7)->T17:(T2:(T7*T8:T7)*T3:T7))"


# fn x => (pair(x(5), x(x(3)))
TOPFREE=0
e = Lambda("x",
        Apply(
            Apply(Identifier("pair"), Apply(Identifier("x"), Identifier("3"))),
                                      Apply(Identifier("x"), Apply(Identifier("x"), Identifier("3")))
            ))
analyse(e, my_env) |> pr == "(T1:(int->T6:T2:int)->T10:(T2:int*T3:int))"


# fn x => (fn y => pair(x, y(x))) (3)
TOPFREE=0
e = Apply(Lambda("x", Lambda("y",
        Apply(
            Apply(Identifier("pair"), Identifier("x")),
                                      Apply(Identifier("y"), Identifier("x"))
        ))), Identifier("3"))
analyse(e, my_env) |> pr == "T10:(T2:(T3:int->T8)->T9:(T3:int*T4:T8))"




# fn x => (pair(x(3) (x(true)))
TOPFREE=0
e = Lambda("x",
        Apply(
            Apply(Identifier("pair"),
                    Apply(Identifier("x"), Identifier("3"))),
            Apply(Identifier("x"), Identifier("true"))))
analyse(e, my_env) |> pr

# pair(f(3), f(true))
TOPFREE=0
e = Apply(
    Apply(Identifier("pair"), Apply(Identifier("f"), Identifier("4"))),
    Apply(Identifier("f"), Identifier("true")))
analyse(e, my_env) |> pr


# let f = (fn x => x) in ((pair (f 4)) (f true))
e = Let("f", Lambda("x", Identifier("x")), pair)
analyse(e, my_env) |> pr


# fn f => f f (fail)
Lambda("f", Apply(Identifier("f"), Identifier("f"))),
try_exp(my_env, e)

# let g = fn f => 5 in g g
e = Let("g",
    Lambda("f", Identifier("5")),
    Apply(Identifier("g"), Identifier("g")))
analyse(e, my_env) |> pr

# example that demonstrates generic and non-generic variables:
# fn g => let f = fn x => g in pair (f 3, f true)
e = Lambda("g",
        Let("f",
            Lambda("x", Identifier("g")),
            Apply(
                Apply(Identifier("pair"),
                        Apply(Identifier("f"), Identifier("3"))
                        ),
                Apply(Identifier("f"), Identifier("true")))))
analyse(e, my_env) |> pr


# Function composition
# fn f (fn g (fn arg (f g arg)))
e = Lambda("f", Lambda("g", Lambda("arg", Apply(Identifier("g"), Apply(Identifier("f"), Identifier("arg"))))))
analyse(e, my_env) |> pr


