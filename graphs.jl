
using LightGraphs, MetaGraphs


# Graphs graphs dfs bfs LightGraphs dac DAC 
A = [
    0 1 1
    1 0 1
    1 1 0
]

G = MetaGraph(Graph(A))
set_props!(mg, 1, Dict(:name=>"Susan", :id => 123))


# REMEMBER: Dijkstra's algorithm === uniform cost search,
# and they pick the child with the SHORTEST distance FROM THE START. A* is this + the heuristic.