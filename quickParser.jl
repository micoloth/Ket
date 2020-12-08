
TOPFREE=100
newvar() = (global TOPFREE = TOPFREE + 1; string(TOPFREE))

# import Pkg; Pkg.add("StaticArrays")
using StaticArrays: SizedArray, SArray, SVector
using StaticArrays

Id = Int
Index = Int
Term = Index

abstract type Data end  #point
abstract type Op end  #function

struct Product <: Data
    data::Array{Data}    
end

struct Sum <: Data
    data::Data
    tag::Index
end

struct Expon <: Data
    func::Op
end

struct Number <: Data
    data::Id    
end


struct Singleton <: Op # already is wired into several things, for convenience
    outputs::Array{Op} 
end

struct Const <: Op # MUST be the Singleton op
    input::Op 
    data::Id
    output::Op
end

struct ConstFunc <: Op  # the difference between Const and this REALLY shouldn't be encoded like this
    # MUST be the Singleton op
    data::Op
    # returns data AS A DATA (into a Comp, presumably)
end

struct Multiapp <: Op
    # input producing a C
    inputFuncs::Op # C->A, C->B, etc  # a TUPLE
    # output A AND B # a TUPLE
end

struct prodElim <: Op  # called Proj
    # input producing a AxB
    # output A OR B- OR MAYBE SOMETHING ELSE ENTIRELY: literally an A, or Literally a B
    tag::Index
end

struct prodIntr <: Op
    # input A TUPLE OF INPUTS: A, B, etc
    # output of Product type
end

struct match <: Op
    inputFuncs::Op # A->C, B->C, etc
    # input an A OR a B
    # output::Op # C
end

struct sumElim <: Op
    # input::Op # of Sum type
    # output::Op # A OR B- OR MAYBE SOMETHING ELSE ENTIRELY: literally an A, or Literally a B
end

struct sumIntr <: Op
    # inputs::Op # ONE OF THESE INPUTS(tagged): A, B, etc
    # output::Op # of Sum type
    tag::Index
end

struct Comp <: Op
    # input::Op 
    functions::Array{Op} # the FUNDAMENTAL FACT is that this is an ORDERED array of funcs
    # output::Op 
end

struct Partial <: Op
    # input::Op
    func::Op
    data::Op # the point is: this is a DATA, NOT A VARIABLE. If you think you want a function here, PREPARE YOURSELF TO HAVE A WHOLE BUNCH OF AN OBJECT IN HERE.
    # output::Op
end
# ^ OR, EQUIVALENTLY (pick one, or if you could pick a "mcd" even better):
struct BuildProd <: Op
    # input::Op
    data::Op # the point is: this is a DATA, NOT A VARIABLE. If you think you want a function here, PREPARE YOURSELF TO HAVE A WHOLE BUNCH OF AN OBJECT IN HERE.
    # output::Op # PRODUCT obj, input x data
end





