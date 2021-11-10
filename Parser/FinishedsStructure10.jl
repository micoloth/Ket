include("SyntaxInst.jl")

# for i in iter   # or  "for i = iter"
#     # body
# end
# next = Base.iterate(iter)
# while next !== nothing
#     (i, state) = next
#     # body
#     next = Base.iterate(iter, state)
# end
# Base.iterate(p::Point) = p.x, [:y, :z]
# function Base.iterate(p::Point, coords)
#    if isempty(coords) nothing
#    else getfield(p, coords[1]), coords[2:end]
#    end
# end
# function c_generator()
#     Channel() do channel
#         for i in 0:5
#             put!(channel, Char('A' + i))
#         end
#     end
# end
# g = c_generator()
# collect(g)
# [g...]




# //Yes, ITS STILL BY MATRIX cuz we're old

# //THERE IS STIL INTERESTING STUFF in >>FinishedStructure<< (from RandomParser9):
# //INCLUDING, a HangingChance10 struct


M_it = Array{Array{Array{SyntaxInstOwner}}}

struct CustomIterForward
	from::UInt
	pos2::UInt
	i::UInt
	# m::M_it
end
getTo(it::CustomIterForward) = it.from + it.pos2 + 1

struct IterableForElementsStartingFrom
	matrix::M_it
	from::UInt
end
Base.IteratorSize(::Type{IterableForElementsStartingFrom}) = Base.SizeUnknown()

function Base.iterate(ifes::IterableForElementsStartingFrom, it::CustomIterForward)::Union{Nothing, Tuple{Tuple{SyntaxInstOwner, Int}, CustomIterForward }}
   if it == CustomIterForward(ifes.from, UInt(length(ifes.matrix[ifes.from+1])), UInt(length(ifes.matrix[ifes.from+1][end]))) nothing
   else
    ((ifes.matrix[it.from+1][it.pos2][it.i+1], it.from + it.pos2 + 1),
     makeFull(ifes.matrix, CustomIterForward(it.from, it.pos2, it.i+1)))
   end
end
function Base.iterate(ifes::IterableForElementsStartingFrom)::Union{Nothing, Tuple{Tuple{SyntaxInstOwner, Int}, CustomIterForward }}
    return Base.iterate(ifes, makeFull(ifes.matrix, CustomIterForward(ifes.from, 1, 0)))
end

function makeFull(m::M_it, it::CustomIterForward)::CustomIterForward
    if (it.pos2 == length(m[it.from+1]) || it.i != length(m[it.from+1][it.pos2])) #//THIS SECOND HERE SHOULD HAVE BEEN CHECKED
        return it
    end
    return makeFull(m, CustomIterForward(it.from, it.pos2 + 1, 0))
end




struct CustomIterBackward
	from::UInt
	to::UInt
	i::UInt
	# m::M_it
end
getFrom(it::CustomIterBackward) = it.from

struct IterableForElementsEndingAt
	matrix::Array{Array{Array{SyntaxInstOwner}}}
	to::UInt
end
Base.IteratorSize(::Type{IterableForElementsEndingAt}) = Base.SizeUnknown()

function Base.iterate(ifee::IterableForElementsEndingAt, it::CustomIterBackward)::Union{Nothing, Tuple{Tuple{SyntaxInstOwner, Int}, CustomIterBackward }}
   if it == CustomIterBackward(ifee.to - 1, ifee.to, UInt(ifee.matrix[ifee.to][1]|>length)) nothing
   else ((ifee.matrix[it.from+1][it.to-it.from][it.i+1], it.from),
         makeFull(ifee.matrix, CustomIterBackward(it.from, it.to, it.i+1)))
   end
end
function Base.iterate(ifee::IterableForElementsEndingAt)::Union{Nothing, Tuple{Tuple{SyntaxInstOwner, Int}, CustomIterBackward }}
    return Base.iterate(ifee, makeFull(ifee.matrix, CustomIterBackward(0, ifee.to, 0)))
end

function makeFull(m::M_it, it::CustomIterBackward)::CustomIterBackward
    if (it.from>=it.to-1 || it.i != length(m[it.from+1][it.to-it.from])) #//THIS SECOND HERE SHOULD HAVE BEEN CHECKED
        return it
    end
    return makeFull(m, CustomIterBackward(it.from +1, it.to, 0))
end


mutable struct FinishedsStructure10  # //SubstringStructureByMatrix
    matrix::Array{Array{Array{SyntaxInstOwner}}}
end



function nullify(FS::FinishedsStructure10, startFrom::Int, stopFrom::Int, startTo::Int, stopTo::Int)  # //to EXCLUDED
    for i in startFrom:(stopFrom-1)
        for j in max(startTo, i):(stopTo-1)
            set(FS, i, j+1, Array{SyntaxInstOwner}([]))
        end
    end
end
function increase(FS::FinishedsStructure10, pos::Int, howMuch::Int)  # //to EXCLUDED
    for i in 0:(pos-1)
        for j in 0:(howMuch-1)
            # FS.matrix[i+1].insert(matrix[i+1].begin() + (pos - i), Array{SyntaxInstOwner}([]));
            FS.matrix[i+1] = vcat(FS.matrix[i+1][1:(pos - i)],  [Array{SyntaxInstOwner}([])], FS.matrix[i+1][(pos - i+1):end])
        end
    end
    L = length(FS.matrix )
    for i in 0:(howMuch-1)
        tt = Array{Array{SyntaxInstOwner}}(undef, L+ 1 + i - pos)
        for i in 1:length(tt) tt[i] = Array{SyntaxInstOwner}([]) end
        FS.matrix = vcat(FS.matrix[1:(pos)],  [tt], FS.matrix[pos+1:end])
    end
end


function remove(FS::FinishedsStructure10, from::Int, to::Int) #//to EXCLUDED
    FS.matrix = vcat(FS.matrix[1:from], FS.matrix[to+1:end])
    for i in 0:(from-1)
        FS.matrix[i+1] = vcat(FS.matrix[i+1][1:(from - i)], FS.matrix[i+1][(to - i + 1):end])
    end
end

FinishedsStructure10() = FinishedsStructure10(0)
function FinishedsStructure10(singletons::Array{SyntaxInstOwner})::FinishedsStructure10
    FS = FinishedsStructure10(length(singletons))
    for (i, s) in enumerate(singletons) push!(FS.matrix[i][1], s) end
    FS
end
function FinishedsStructure10(rows::Int)::FinishedsStructure10
    FS = Array{Array{Array{SyntaxInstOwner}}}(undef, rows)
    for i in 1:length(FS)
        FS[i] = Array{Array{SyntaxInstOwner}}(undef, rows-i+1)
        for j in 1:length(FS[i])
            FS[i][j] = Array{SyntaxInstOwner}([])
        end
    end
    FinishedsStructure10(FS)
end

size(FS::FinishedsStructure10)::Int = length(FS.matrix)


at(FS::FinishedsStructure10, from::Int, to::Int)::Array{SyntaxInstOwner} = FS.matrix[from+1][(to-1)-from+1] # //to EXCLUDED
function set(FS::FinishedsStructure10, from::Int, to::Int, what)
    FS.matrix[from+1][(to-1)-from+1] = what  # //to EXCLUDED
end
function add(FS::FinishedsStructure10, from::Int, to::Int, what)
    push!(FS.matrix[from+1][(to-1)-from+1], what)  # //to EXCLUDED
end




function reshape(FS::FinishedsStructure10, from::Int, to::Int, howMuch::Int)  #//to EXCLUDED
    if (howMuch < to - from)
        remove(FS, from + howMuch, to)
        nullify(FS, 0, from + howMuch, from, length(FS.matrix))  # //HERE IS WHERE MAYBE THERES HOPE //not like this, of course, there isn't
    else
        increase(FS, to, howMuch - (to - from))
        nullify(FS, 0, to, from, length(FS.matrix))  # //HERE IS WHERE MAYBE THERES HOPE
    end
end

function trace(FS::FinishedsStructure10)
    for i in 1:(FS.matrix|>length)
        for j in 1:(FS.matrix[i]|>length)
            if length(FS.matrix[i][j])>0
                print("($(i-1),$(i+j-1)) $(join(FS.matrix[i][j] .|> trace, " || ")) ")
            end
        end
        println("")
    end
end
EverythingBeginningAt(FS::FinishedsStructure10, from::UInt) = IterableForElementsStartingFrom(FS.matrix, from)  #//from INCLUDED
EverythingEndingAt(FS::FinishedsStructure10, to::UInt) = IterableForElementsEndingAt(FS.matrix, to)  #//to EXCLUDED??-- it's the BEGINNING OF THE NEXT .


function getBestTotalFound(FS::FinishedsStructure10)::Union{SyntaxInstOwner, Nothing}
    if (length(FS.matrix) == 0) nothing
    elseif (at(FS, 0, length(FS.matrix)) |> length == 0) # //WROONG   # ??????
        nothing
    else at(FS, 0, length(FS.matrix))[1]
    end
end
