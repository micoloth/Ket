  
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
    # instance::Union{Nothing, Type_}
    name::String
end

TypeVariable() = (v = newvar(); TypeVariable(v, string(v)))
# TypeVariable() = (v = newvar(); TypeVariable(v, nothing, string(v)))

struct TypeOperator<:Type_
    name::String
    types::Array{Type_}
end
struct Function<:Type_
    instances::Dict{String, Type_}
    from_type::Type_ 
    to_type::Type_
end
# Function(from_type, to_type)::TypeOperator = TypeOperator("->", [from_type, to_type])
Function(from_type, to_type)::Function = Function(Dict{Index, Type_}(), from_type, to_type)

Integer_() = TypeOperator("int", [])  # Basic integer
Bool_() = TypeOperator("bool", [])  # Basic bool

pr(t::TypeVariable)::String = "T"*t.name # t.instance===nothing ? "T"*t.name : "T"*t.name*":"*(t.instance |> pr)
pr(t::TypeOperator)::String = isempty(t.types) ? t.name : "($(join(t.types .|> pr, t.name)))"
pr(t::Function)::String = "($(t.from_type |> pr)->$(t.to_type |> pr))" * (t.instances |> length == 0 ? "" : " where "*join(["T"*k*":"*pr(v) for (k,v) in t.instances], ", "))

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


function analyse(node::Identifier, env::Dict{String, Type_}, non_generic::Array{Type_}=Array{Type_}([]))
    return get_type(node.name, env, non_generic)
end
function analyse(node::Apply, env, non_generic::Array{Type_}=Array{Type_}([]))
    # println("env: ", [k*":"*pr(v) for (k, v) in env])
    # println("non_generic: ", non_generic .|> pr)
    fun_type = analyse(node.fn, env, non_generic)
    arg_type = analyse(node.arg, env, non_generic)
    result_type = TypeVariable() ################################ EXTREMELY IMPORTANT THING that is happening!!! (it's what's broken in the Other One)
    unify(prune(Function(arg_type, result_type), env), prune(fun_type, env), env)
    return result_type
end
function analyse(node::Lambda, env::Dict{String, Type_}, non_generic::Array{Type_}=Array{Type_}([]))
    # println("env: ", [k*":"*pr(v) for (k, v) in env])
    # println("non_generic: ", non_generic .|> pr)
    arg_type = TypeVariable()
    new_env = copy(env)
    new_env[node.v] = arg_type
    new_non_generic = copy(non_generic)
    push!(new_non_generic, arg_type)
    result_type = analyse(node.body, new_env, new_non_generic)
    return Function(new_env, arg_type, result_type)
end
function analyse(node::Let, env::Dict{String, Type_}, non_generic::Array{Type_}=Array{Type_}([])) #dc
    # println("env: ", [k*":"*pr(v) for (k, v) in env])
    # println("non_generic: ", non_generic .|> pr)
    defn_type = analyse(node.defn, env, non_generic)
    new_env = copy(env)
    new_env[node.v] = defn_type
    return analyse(node.body, new_env, non_generic)
end
function analyse(node::Letrec, env::Dict{String, Type_}, non_generic::Array{Type_}=Array{Type_}([])) #dc
    # println("env: ", [k*":"*pr(v) for (k, v) in env])
    # println("non_generic: ", non_generic .|> pr)
    new_type = TypeVariable()
    new_env = copy(env)
    new_env[node.v] = new_type
    new_non_generic = copy(non_generic)
    push!(new_non_generic, new_type)
    defn_type = analyse(node.defn, new_env, new_non_generic)
    unify(prune(new_type, env), prune(defn_type, env), env)
    return analyse(node.body, new_env, non_generic)
end


################# 

function get_type(name, env, non_generic)
    # """Get the type of identifier name from the type environment env.
    if name in keys(env)
        return fresh(env[name], non_generic, env)
    elseif is_integer_literal(name)
        return Integer_()
    else
        throw(ParseError("Undefined symbol $(name)"))
    end
end



function fresh(t, non_generic, ctxout::Dict{String, Type_})
    # Makes a copy of a type expression.
    # The type t is copied. The the generic variables are duplicated and the
    # non_generic variables are shared.
    mappings = Dict{TypeVariable, TypeVariable}()  # A mapping of TypeVariables to TypeVariables
    
    function freshrec(tp, ctx::Dict{String, Type_})
        p = prune(tp, ctx)
        if p isa TypeVariable
            if is_generic(p, non_generic, ctx)
                get!(mappings, p, TypeVariable()) 
                #The the generic variables are duplicated, the old->new map is stored in Mappings so that same olds have same news.  Mappings is != from env !!!!!!
            else
                p
            end
        elseif p isa TypeOperator
            return TypeOperator(p.name, [freshrec(x, ctx) for x in p.types])
        elseif p isa Function
            return Function(freshrec(p.from_type, ctx), freshrec(p.to_type, ctx))
        end
    end
    
    freshrec(t, ctxout)
end


# Unify the two types t1 and t2.
# Makes the types t1 and t2 the same.
# a = prune(t1)
# b = prune(t2)
function unify(a::TypeVariable, b::Type_, ctx::Dict{String, Type_})
    if a != b
        if occurs_in_type(a, b, ctx)
            throw(InferenceError("recursive unification"))
        end
        ctx[a.name] = b
    end
end
function unify(a::TypeVariable, b::TypeVariable, ctx::Dict{String, Type_}) # SAME as above
    if a != b
        if occurs_in_type(a, b, ctx)
            throw(InferenceError("recursive unification"))
        end
        ctx[a.name] = b
    end
end
function unify(a::Type_, b::TypeVariable, ctx::Dict{String, Type_}) 
    unify(b, a, ctx)
end
function unify(a::TypeOperator, b::TypeOperator, ctx::Dict{String, Type_}) 
    if (a.name != b.name) || (length(a.types) != length(b.types))
        throw(InferenceError("Type mismatch: $(a) != $(b)"))
    end
    for (p, q) in zip(a.types, b.types, ctx::Dict{String, Type_})
        unify(prune(p, ctx), prune(q, ctx), ctx)
    end
end
function unify(a::Function, b::Function, ctx::Dict{String, Type_}) 
    for (p, q) in zip([a.from_type, a.to_type], [b.from_type, b.to_type])
        unify(prune(p, a.instances), prune(q, b.instances), ctx) ################ THIS is there i think it should have a SECOND (TYPE) LEVEL APPLY.......
    end
end
function unify(a, b, ctx::Dict{String, Type_}) 
    throw(DomainError("There are other cases?? ($(a)  <- and -> $(b))"))
end

# """Returns the currently defining instance of t.
# As a side effect, collapses the list of type instances. The function Prune
# is used whenever a type expression has to be inspected: it will always
# return a type expression which is either an uninstantiated type variable or
# a type operator; i.e. it will skip instantiated variables, and will
# actually prune them from expressions to remove long chains of instantiated
# variables.

# Here, pruning is NOT pruning tho: this is because you DONT have the FULL context stack :(
function prune(t::Type_, context::Dict{String, Type_})
    if (t isa TypeVariable) get(context, t.name, t)
    else t
    end
end
        
# function prune(t::Type_)
#     if ((t isa TypeVariable) && (t.instance !== nothing))
#         t.instance = prune(t.instance)
#         return t.instance
#     end
#     return t
# end

# """Checks whether a given variable occurs in a list of non-generic variables.
# This means: that a given type-VARIABLE v either IS, or IS USED BY (is THE INSTANCE OF A VARIABLE IN) type type2 in non_generic ...
# OR, that a given variable is used somewhere AS A FINAL VALUE (is EITHER tha var itself OR an instance) , INSTEAD OF AS A variable

# [[recursively in nested contexts]]
# Note: Must be called with v pre-pruned

function is_generic(v, non_generic, ctx::Dict{String, Type_})
    return ! occurs_in(v, non_generic, ctx)
end

function occurs_in_type(v, type2, ctx::Dict{String, Type_})
    # """Checks whether a type variable occurs in a type expression.
    # Note: Must be called with v pre-pruned
    pruned_type2 = prune(type2, ctx)
    if pruned_type2 == v
        return true
    elseif pruned_type2 isa TypeOperator
        return occurs_in(v, pruned_type2.types, ctx)
    elseif pruned_type2 isa Function
        return occurs_in(v, [pruned_type2.from_type, pruned_type2.to_type], pruned_type2.instances)
    end
    return false
end

function occurs_in(t, types, ctx::Dict{String, Type_})
    return [occurs_in_type(t, t2, ctx) for t2 in types] |> any
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
my_env = Dict{String, Type_}("pair"=> Function(var1, Function(var2, pair_type)))

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
analyse(e, my_env) |> pr == "(T1:(int->T6:T2:T3)->T9:(T2:T3*T3))"

# fn x => (pair((y=>pair(y y))(3) (x(5)))
TOPFREE=0
e = Lambda("x",
        Apply(
            Apply(Identifier("pair"),
                    Apply(Lambda("y", Apply(Apply(Identifier("pair"), Identifier("y")), Identifier("y"))), Identifier("3"))),
            Apply(Identifier("x"), Identifier("5"))))
analyse(e, my_env) |> pr == "(T1:(int->T15:T3)->T16:(T2:(T7:int*T8:int)*T3))"

# fn x => (pair((y=>pair(y y))(x(3)) (x(5)))
TOPFREE=0
e = Lambda("x",
        Apply(
            Apply(Identifier("pair"),
                    Apply(Lambda("y", Apply(Apply(Identifier("pair"), Identifier("y")), Identifier("y"))), Apply(Identifier("x"), Identifier("3")))),
            Apply(Identifier("x"), Identifier("5"))))
analyse(e, my_env) |> pr == "(T1:(int->T13:T8:T3)->T17:(T2:(T7:T3*T8:T3)*T3))"


# fn x => (pair(x(5), x(x(3)))
TOPFREE=0
e = Lambda("x",
        Apply(
            Apply(Identifier("pair"), Apply(Identifier("x"), Identifier("3"))),
                                      Apply(Identifier("x"), Apply(Identifier("x"), Identifier("3")))
            ))
analyse(e, my_env) |> pr == "(T1:(int->T6:T2:int)->T10:(T2:int*T3:int))"


# fn x => (fn y => pair(x, y(x))) (3) #[3 is applied to x]
TOPFREE=0
e = Apply(Lambda("x", Lambda("y",
        Apply(
            Apply(Identifier("pair"), Identifier("x")),
                                      Apply(Identifier("y"), Identifier("x"))
        ))), Identifier("3"))
analyse(e, my_env) |> pr == "T10:(T2:(T3:int->T8:T4)->T9:(T3:int*T4))"




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


