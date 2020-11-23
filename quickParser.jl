
TOPFREE=100
newvar() = (global TOPFREE = TOPFREE + 1; string(TOPFREE))

# import Pkg; Pkg.add("StaticArrays")
using StaticArrays: SizedArray, SArray, SVector
using StaticArrays

Id = Int
Index = Int
Term = Index

abstract type Op end  #node  # BIDIRECTIONAL graph

struct Prod <: Op # introduction
    inputs::Array{Op}
    output::Op # this CAN be: a PROJ, OR a thing that carries the thing around
    tag::Index 
end

struct Sum <: Op  # also called: Drop
    input::Op
    output::Op
    tag::Index 
end

struct Proj <: Op  # also called: Drop
    inputs::Op  # MUST BE A PRODUCT (or a local var / pipe)
    output::Op
    tag::Index 
end

struct Match <: Op 
    input::Op # MUST BE A SUM (or a local var / pipe)
    paths::Array{Op} # only takes ONE tho  # also: i want to GUARANTEE that these 2 GO IN THE SAME OUTPUT after 1 step
    output:: Op
end

struct Compose <: Op 
    input::Op
    output:: Op
    ops::Array{Op} # fundamental fact: this is ORDERED!!!
end  

struct MonPair <: Op  # monoidal product of 2 ops (do them in parallel)
    ops::Array{Op}
end 

struct Number <: Op
    output::Op
    n::Id
end

struct Dupl <: Op  # This is the Essence of reusing a var! I'm sure it's some universal construction 
                   #(remember: Universal Construction vs Polymorphic Type specification!)
    input::Op
    outputs::Array{Op}
    n::Index 
end

struct Loop # nfold. The idea is that is (slightly) more complex because THIS DOESN'T EXIST WITHOUT RELYING ON REPRESENTATION!
    input::Op
    output::Op
    op::Op
    n::Index
    # question: WHY is this different than the one you could (?) build with Dupl + Compose ?
end


struct Result <: Op
    input::Op
end

struct LocalVar # this is actutally an EMPTY TOKEN (available pipe)
    output::Array{Op} 
end

# NOT abstract type Map <: Op end: this is a higher order func

Pkg.add("GraphPlot")

dupliStatus = Dict{Dupl, Tuple{Int, Int}}  # Status, Name
composeStatus = Dict{Compose, Int}  # Status, Name

pri(t::Match)::String = "$(t.input) if $(t.tag)?{0\\$(pri(t.paths[0])), 1\\$(pri(t.paths[0]))}"
pri(t::Proj)::String = "[$(t.tag)]"   # $(join(t.inputs .|> pri, " ,  ")))
pri(t::Compose)::String = "{x.$(join(t.ops .|> pri, '.'))}"
pri(t::MonPair)::String = join(t.ops .|> pri, " x ")
pri(t::Number)::String = "$(n)"
pri(t::Result)::String = "$(t.input |> pri).compute"
function pri(t::Dupl)::String
    tst = get(dupliStatus, t, Nothing)
    if tst!== Nothing
        tst[0] += 1
        if tst[0] < t.n
            "$(tst[1])"
        else
            "$(tst[1]) where $(tst[1])=$(t.input |>pri)"
        end
    else
        x=newvar()
        dupliStatus[t] = (0, x)
        x
    end
end

addEdge!(t::Match, g::DiGraph) = "Match $(t.tag)" 
addEdge!(t::Proj, g::DiGraph) = "Proj $(t.tag)" 
addEdge!(t::Compose, g::DiGraph) = (x=get!(composeStatus, t, newvar()); "Compose $()")#################
addEdge!(t::MonPair, g::DiGraph) = "" ############## again, these are different edges 
addEdge!(t::Number, g::DiGraph) = "Number $(t.n)" 
addEdge!(t::Result, g::DiGraph) = "Result" 
addEdge!(t::Dupl, g::DiGraph) = "Dupl $()"  



using GraphPlot

using LightGraphs: smallgraph, nv, ne
using LightGraphs


g=SimpleDiGraph()
add_vertex!(g)
add_edge!(g, 1, 2)

g
g = smallgraph(:karate)

nodelabel = 1:nv(g)
edgelabel = ["LABEL"*string(l) for l in 1:ne(g)]
gplot(g, nodelabel=nodelabel, edgelabel = edgelabel, layout=stressmajorize_layout)





#########################################

run(op1::Number, op2::Match) = run(op1.n, (op1.n == 0) ? (op2.paths[0]) : (op2.paths[1]))
run(op1::Number, op2::)
