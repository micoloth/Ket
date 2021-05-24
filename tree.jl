

struct Node{T}
    idx::Int
    val::T
    parent::Union{Int, Nothing}
    children::Array{Int}
end
struct Tree{T}
    data::Array{Node{T}}
end


edges(tree::Tree{T}) where {T} = tree.data .|> (x->x.children |> length) |> sum
size(tree::Tree{T}) where {T} = tree.data |> length
depth(tree::Tree{T}, node_id::Int) where {T} = (p = tree.data[node_id].parent; (p isa Int) ? (1 + depth(tree, p)) : 0)


function depth_to_target_DFS(tree::Tree{T}, idx::Int, target::T)::Union{Int, Nothing} where {T}
    if target == tree.data[idx].val return 1 end
    for i in tree.data[idx].children
        res = depth_to_target_DFS(tree, i, target)
        if res !== nothing return res + 1 end
    end
    nothing
end

function insert!(tree::Tree{T}, parent_idx::Int, val::T) where {T}
    node = Node{T}(tree.data |> length + 1, val, parent_idx, [])
    push!(tree.data[parent_idx].children, tree.data |> length + 1)
    push!(tree.data, node)
end

function pr(t::Tree{T}, start_idx::Int, print_fun) where {T}
    val = print_fun !== nothing ? print_fun(t.data[start_idx].val) : t.data[start_idx].val
    childs = t.data[start_idx].children .|> (x->pr(t, x, print_fun)) |> (x->join(x, ", "))
    if childs |> length > 0 childs = "->" * childs end  # childs = childs .{"": nop, s: "->"*s}
    "{" * val * childs * "}"
end
pr(t::Tree{T}, print_fun=nothing) where {T} = pr(t, 1, print_fun)

tree = Tree{String}([Node{String}(1,"hi",nothing, [2, 3]), Node{String}(2,"Tom",1, []), Node{String}(3,"Greg",1, [])])
size(tree), edges(tree), depth(tree, 2)
depth_to_target_DFS(tree, 1, "Greg")
pr(tree, 1, nothing)
pr(tree)

start_idx=2

pr(t, 2, print_fun)