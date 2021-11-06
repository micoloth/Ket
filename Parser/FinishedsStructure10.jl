
# for i in iter   # or  "for i = iter"
#     # body
# end
# next = iterate(iter)
# while next !== nothing
#     (i, state) = next
#     # body
#     next = iterate(iter, state)
# end
# iterate(p::Point) = p.x, [:y, :z]
# function iterate(p::Point, coords)
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


M_it = Array{Array{Array{SyntaxInst}}}

struct CustomIterForward
	from::UInt
	pos2::UInt
	i::UInt
	# m::M_it
end
getTo(it::CustomIterForward) = it.from + it.pos2 + 1
CustomIterForward(from::Uint, to::Uint, i::Uint)  = CustomIterForward(from, to - from - 1, i)

struct IterableForElementsStartingFrom
	matrix::M_it
	from::Uint
end
function iterate(ifes::IterableForElementsStartingFrom)
    from, pos2, i = ifes.from, ifes.from+1, 0
    return (ifes.matrix[from+1][pos2+1][i+1], makeFull(ifes.matrix, CustomIterForward(from, pos2, i+1)))
end
function iterate(ifes::IterableForElementsStartingFrom, it::CustomIterForward)
   if it == CustomIterForward(ifes.from, Uint(length(ifes.matrix)), Uint(length(ifes.matrix[ifes.from+1][end]))) nothing
   else ifes.matrix[from+1][pos2+1][i+1], makeFull(ifes.matrix, CustomIterForward(it.from, it.pos2, it.i+1))
   end
end

function makeFull(m::M_it, it::CustomIterForward)::CustomIterForward
    if (it.i != length(m[from+1][pos2+1]) || it.pos2 == length(m[it.from+1]) - 1) #//THIS SECOND HERE SHOULD HAVE BEEN CHECKED
        return it
    end
    it.pos2 +=1
    it.i = 0
    return makeFull(m, it);
end




struct CustomIterBackward
	from::UInt
	to::UInt
	i::UInt
	# m::M_it
end
getFrom(it::CustomIterBackward) = it.from
CustomIterBackward(from::UInt, to::UInt, i::UInt) =CustomIterBackward(from(from), to(to), i(i))

struct IterableForElementsEndingAt
	matrix::Array{Array{Array{SyntaxInst}}}
	to::Uint
end
function iterate(ifee::IterableForElementsEndingAt)
    from, to, i = 0, ifee.to, 0
    (ifee.matrix[from+1][to-from][i+1], makeFull(ifee.matrix, CustomIterBackward(from, to, i+1)))
end
function iterate(ifee::IterableForElementsEndingAt, it::CustomIterBackward)
   if it == CustomIterBackward(ifee.to - 1, ifee.to, Uint(ifee.matrix[ifee.to][1]|>length)) nothing
   else ifee.matrix[from+1][to-from][i+1], makeFull(ifee.matrix, CustomIterBackward(it.from, it.to, it.i+1))
   end
end

function makeFull(m::M_it, it::CustomIterBackward)::CustomIterBackward
    if (it.from>=it.to-1 || it.i != length(m[it.from+1][it.to-it.from])) #//THIS SECOND HERE SHOULD HAVE BEEN CHECKED
        return it
    end
    it.from +=1
    it.i = 0
    return makeFull(m, it);
end



T = Array{SyntaxInst}
struct FinishedsStructure10  # //SubstringStructureByMatrix
    matrix::Array{Array{T}}
end



function nullify(FS::FinishedsStructure10, startFrom::Int, stopFrom::Int, startTo::Int, stopTo::Int)  # //to EXCLUDED
    for i in startFrom:(stopFrom-1)
        for j in max(startTo, i):(stopTo-1)
            set(FS, i, j+1, T([]))
        end
    end
end
function increase(FS::FinishedsStructure10, pos::Int, howMuch::Int)  # //to EXCLUDED
    for i in 0:(pos-1)
        for j in 0:(howmuch-1)
            # FS.matrix[i+1].insert(matrix[i+1].begin() + (pos - i), T([]));
            FS.matrix[i+1] = vcat(FS.matrix[i+1][1:(pos - i-1)],  [T([])], FS.matrix[i+1][(pos - i):end])
        end
    end
    for i in 0:(howMuch-1)
        tt = Array{T}(undef, length(FS.matrix + 1) + i - pos)
        for i in 1:length(tt) tt[i] = T([]) end
        FS.matrix = vcat(FS.matrix[1:(pos-1)],  tt, FS.matrix[pos:end])
    end
end


function remove(FS::FinishedsStructure10, from::Int, to::Int) #//to EXCLUDED
    FS.matrix = vcat(FS.matrix[1:from], FS.matrix[to+1:end])
    for i in 0:(from-1)
        FS.matrix[i+1] = vcat(FS.matrix[i+1][1:(from - i)], FS.matrix[i+1][(to - i + 1):end])
    end
end


function FinishedsStructure10(singletons::T)::FinishedsStructure10
    FS = FinishedsStructure10(length(singletos))
    for (i, s) in enumerate(singletons) push!(FS.matrix[i+1][i+1], s) end
    FS
end
function FinishedsStructure10(rows::Int)::FinishedsStructure10
    FS = Array{Array{T}}(undef, rows)
    for i in 1:length(FS)
        FS[i] = Array{T}(undef, rows)
        for j in 1:length(FS[i])
            FS[i][j] = T([])
        end
    end
    FinishedsStructure10(FS)
end

size(FS::FinishedsStructure10)::Int = length(FS.matrix)


at(FS::FinishedsStructure10, from::Int, to::Int) = FS.matrix[from+1][(to-1)-from +1] # //to EXCLUDED
set(FS::FinishedsStructure10, from::Int, to::Int, what) = (FS.matrix[from+1][(to-1)-from +1] = what)  # //to EXCLUDED
add(FS::FinishedsStructure10, from::Int, to::Int, what) = (FS.matrix[from+1][(to-1)-from +1] = what)  # //to EXCLUDED




function reshape(FS::FinishedsStructure10, from::Int, to::Int, howMuch::Int)  #//to EXCLUDED
    if (howMuch < to - from)
        remove(FS, from + howMuch, to)
        nullify(FS, 0, from + howMuch, from, matrix.size())  # //HERE IS WHERE MAYBE THERES HOPE //not like this, of course, there isn't
    else
        increase(FS, to, howMuch - (to - from))
        nullify(FS, 0, to, from, matrix.size())  # //HERE IS WHERE MAYBE THERES HOPE
    end
end

function trace(FS::FinishedsStructure10)
    for i in 1:(FS.matrix|>length)
        for j in in 1:(FS.matrix[i]|>length)
            print("($(i),$(i+j+1)): $(join(FS.matrix[i][j] .|> print, " ")) ")
        end
        println("")
    end
end
EverythingBeginningAt(FS::FinishedsStructure10, from::Uint) = IterableForElementsStartingFrom(FS.matrix, from)  #//from INCLUDED
EverythingEndingAt(FS::FinishedsStructure10, to::Uint) = IterableForElementsEndingAt(FS.matrix, to)  #//to EXCLUDED??-- it's the BEGINNING OF THE NEXT .


function getBestTotalFound(FS::FinishedsStructure10)::Union{SyntaxInst, Nothing}
    if (length(FS.matrix) == 0) nothing
    elseif (at(FS, 0, length(FS.matrix)) |> length == 0) # //WROONG   # ??????
        nothing
    else at(FS, 0, length(FS.matrix))[1]
    end
end
