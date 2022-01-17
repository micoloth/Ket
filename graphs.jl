
using Graphs, MetaGraphs


# Graphs graphs dfs bfs Graphs dac DAC
A = [
    0 1 1
    1 0 1
    1 1 0
]

G = MetaGraph(Graph(A))
set_props!(mg, 1, Dict(:name=>"Susan", :id => 123))


# REMEMBER: Dijkstra's algorithm === uniform cost search,
# and they pick the child with the SHORTEST distance FROM THE START. A* is this + the heuristic.














import Pkg; Pkg.add("MetaGraphs")
using Graphs
using MetaGraphs

# nv: Returns number of vertices in graph.
# ne: Returns number of edges in graph.
# vertices: Iterable object of all graph vertices.
# edges: Iterable object of all graph edges.
# has_vertex: Checks for whether graph includes a vertex.
# has_edge(g, s, d): Checks for whether graph includes an edge from a given source s to a given destination d.
# has_edge(g, e): will return true if there is an edge in g that satisfies e == f for any f ∈ edges(g)
# has_self_loops

# Vertex Properties
# neighbors: Return array of neighbors of a vertex. If graph is directed, output is equivalent of outneighbors.
# all_neighbors: Returns array of all neighbors (both inneighbors and outneighbors). For undirected graphs, equivalent to neighbors.
# inneighbors: Return array of in-neighbors. Equivalent to neighbors for undirected graphs.
# outneighbors: Return array of out-neighbors. Equivalent to neighbors for undirected graphs.
# Edge Properties
# src: Give source vertex of an edge.
# dst: Give destination vertex of an edge.
# reverse: Creates a new edge running in opposite direction of passed edge.
# « Graphs Types


parent_(p)=p[1]
children_(p)=p[2]


list_of_nodes = Array{Pair}(["v3"=>["v4", "v5"], "v2"=>["v3"], "v1"=>["v2", "v3"], "v4"=>[]])

order_list_of_nodes(list_of_nodes)

function order_list_of_nodes(list_of_nodes)
    parents = list_of_nodes .|> parent_
    g = SimpleDiGraph(length(parents))
    pos_dict = Dict(word=>i for (i, word) in enumerate(parents))
    @assert length(unique(parents)) == length(parents)
    for node in list_of_nodes
        for c in children_(node)
            if c in parents
                add_edge!(g, pos_dict[c], pos_dict[parent_(node)])
            end
        end
    end
    @assert !is_cyclic(g)
    order = topological_sort_by_dfs(g)
    [list_of_nodes[i] for i in order]
end


add_edge!(g, 1, 3)
add_edge!(g, 2, 3)
has_self_loops(g) # false
is_cyclic(g) # false

roots = [v for v in vertices(g) if inneighbors(g, v)|>length ==0]


# WITH METATAGS:




g = MetaDiGraph(3)
set_indexing_prop!(g, :name)
for (i,s) in enumerate(["a", "b", "c"])
    set_prop!(g, i, :name, s)
end
# nodes can now be found by the value in the index
g["a", :name]

add_edge!(g, g["a", :name], g["b", :name])
add_edge!(g, g["a", :name], g["c", :name])
add_edge!(g, g["b", :name], g["c", :name])





