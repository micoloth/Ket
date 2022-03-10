
include("Structure11.jl")

# text = "ff:(A->B)-> B  where ff (  g  )  =  g  (  a )  eval ff ( h ) "

struct Substit
	oldFrom::Int
    oldTo::Int
    newFrom::Int
    newTo::Int
end
getOld(ss::Substit) = (ss.oldFrom, ss.oldTo)

mutable struct RandomParser10
    inputText::String
	inputVec::Array{String}
    structure::Structure11
end
RandomParser10() = RandomParser10("", [], Structure11())


do_parse(prs::RandomParser10, s::String) = updateInput(prs, s)
function updateInput(prs::RandomParser10, newText::String)
    if (prs.inputText == newText) return end
    prs.inputText = newText
    newVec = getTextVector(newText)
    s::Substit = getSubstit(newVec, prs.inputVec)  # to Not included
    if (s.oldTo <= s.oldFrom && s.newTo <= s.newFrom) return end
    prs.inputVec = newVec
    prs.structure.inputVec= prs.inputVec
    updateStructure(prs, s)
end

function matchTerminals(prs::RandomParser10, from_::Int, end_::Int)  # # [..)
	for i in from_:(end_-1)
		t = getTerminal(prs.structure.posteriorsStructure, prs.inputVec[i+1]) # TODO CHECK what the type of this is !!!! Should be a Pair, at least
		if (t[1] !== nothing) insertTerminal(prs.structure, i, i+1, t[1], t[2]) end
        t = getGlobal(prs.structure.posteriorsStructure, prs.inputVec[i+1]) # TODO CHECK what the type of this is !!!! Should be a Pair, at least
		if (t[1] !== nothing) insertGlobal(prs.structure, i, i+1, prs.inputVec[i+1], t[1], t[2]) end
        if tryparse(Int, prs.inputVec[i+1]) !== nothing  insertNumber(prs.structure, i, i+1, prs.inputVec[i+1], 0.5)  end # Add numbers
    end
end

function updateStructure(prs::RandomParser10, s::Substit)
	reshape(prs.structure, s.oldFrom, s.oldTo, s.newTo - s.newFrom) # TODO reshape-> reshape_struct, check everything's ok
	matchTerminals(prs, s.newFrom, s.newTo)#, { newVec.begin() + s.newFrom,newVec.begin() + s.newTo })
	trace(prs.structure)
	doTheBestYouCan(prs.structure)
	showstructure(prs)
end


showstructure(prs::RandomParser10) = trace(prs.structure)
getBestTotalFound(prs::RandomParser10) = getBestTotalFound(prs.structure)


getString(v::Array{String}) :: String = join(v, "")
function getTextVector(s::String)::Array{String}
    # POTENTIAL OPTIMIZATION: make this not dumb
    for c in s if !(isnumeric(c) || isletter(c) || c==' ') s=replace(s, c=> " $(c) ") end end
    return filter(x->(length(x) > 0), split(s, " "))
end

function getSubstit(newVec::Array{String}, oldVec::Array{String})::Substit
	for i in 1:min(length(newVec), length(oldVec))
		if (newVec[i] != oldVec[i]) break end
    end
	oldFrom = min(length(newVec), length(oldVec))
	newFrom = min(length(newVec), length(oldVec))
	for i in 1:min(length(newVec), length(oldVec))
		if (newVec[length(newVec) - i] != oldVec[length(oldVec) - i]) break end
    end
	oldTo = length(oldVec) - min(length(newVec), length(oldVec))
	newTo = length(newVec) - min(length(newVec), length(oldVec))
	return Substit(oldFrom, oldTo, newFrom, newTo)
end
