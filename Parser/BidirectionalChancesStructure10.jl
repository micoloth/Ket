

struct HangingChance10
	previouses::Array{HangingChance10}
	nexts::Array{HangingChance10}
	chance::SyntaxProduct
	object::SyntaxInst
	indexInChance::Int  # //in strips it is the code
	length::Int  # //of object

	marginalOfChance::Real
	MarginalOfCurrObjName::Real
	POfThisIfGoingForward::Real
	POfThisIfGoingBackward::Real
end
HangingChance10(
    chance::SyntaxProduct, object::SyntaxInst, indexInChance::Int,
    length::Int, marginalOfChance::Real, MarginalOfCurrObjName::Real) = HangingChance10(
        Array{HangingChance10}([]), Array{HangingChance10}([]),
        chance, object, indexInChance, length, marginalOfChance, MarginalOfCurrObjName,
        getP(object) / MarginalOfObjName, getP(object) / MarginalOfObjName,
    )

getTo(hc::HangingChance10, from::Int) = from + hc.length
getFrom(hc::HangingChance10, to::Int) = to - hc.length
hasEnded(hc::HangingChance10)::bool = getPossibleNexts(hc.chance, getName(hc.object, hc.indexInChance+1)) |> isempty  # +1, apparently
hasJustBegun(hc::HangingChance10)::bool = getPossiblePreviouses(hc.chance, getName(hc.object, hc.indexInChance)) |> isempty
# SyntaxProduct getChance() { return chance; }
# int getIndexInChance() { return indexInChance; }
# float getPForward() { return POfThisIfGoingForward; }
# float getPBackward() { return POfThisIfGoingBackward;	}



function getFinalObjsFromEnd(hc::HangingChance10)::Array{Tuple{Int, SyntaxInstProductOwning}}
    if (hasJustBegun(hc))
        newTemp = SyntaxInstProductOwning(hc.chance, hc.marginalOfChance)
        push_back(newTemp, hc.object, hc.indexInChance, hc.MarginalOfCurrObjName)
        tempList = Array{Tuple{Int, SyntaxInstProductOwning}}([(length, newTemp)])
        return tempList
    else
        buildswSizes = Array{Tuple{Int, SyntaxInstProductOwning}}([])
        for p in hc.previouses
            if p  # btw "if (p)",  SHOULD HAVE BEEN CHECKED ALREADY!!.
                append!(buildswSizes, getFinalObjsFromEnd(p))
            end
        end
        for v in buildswSizes
            v[1] += length
            push_back(v[2], hc.object, hc.indexInChance(), hc.MarginalOfCurrObjName);
        end
    end
    return buildswSizes
end


# //this one, COULD BE BETTER
function getFinalObjsFromStart(hc::HangingChance10)::Array{Tuple{Int, SyntaxInstProductOwning}}
    if hasEnded(hc)
        newTemp = SyntaxInstProductOwning(hc.chance, hc.marginalOfChance)
        insert_front(newTemp, hc.object, hc.indexInChance, hc.MarginalOfCurrObjName);
        tempList =  Array{Tuple{Int, SyntaxInstProductOwning}}([(length, newTemp)])
        return tempList
    else
        buildswSizes = Array{Tuple{Int, SyntaxInstProductOwning}}([])
        for p in hc.previouses
            if p #  // btw "if (p)", SHOULD HAVE BEEN CHECKED ALREADY!!.
                append!(buildswSizes,getFinalObjsFromStart(p))
            end
        end
        for v in buildswSizes
            v[1] += length;
            insert_front(v[2], hc.object, hc.indexInChance, hc.MarginalOfCurrObjName)
        end
    end
    return buildswSizes
end



getWhatNeedBefore(hc::HangingChance10)::Array{SyntaxCore} = getPossiblePreviouses(hc.chance, hc.object.getName(), hc.indexInChance)
getWhatNeedNext(hc::HangingChance10)::Array{SyntaxCore} = getPossibleNexts(hc.chance, hc.object.getName(), hc.indexInChance+1) # +1, apparently
needsBefore(hc::HangingChance10, obj::SyntaxCore)::Int = obj in getWhatNeedBefore(hc)
needsNext(hc::HangingChance10, obj::SyntaxCore)::Int = obj in getWhatNeedNext(hc)


function linkWithThisPrevious!(hc::HangingChance10, prev::HangingChance10) # God i HOPE references work as they sauy they do ...
    push!(hc.previouses, prev)
    push!(prev.nexts, hc)
    prev.POfThisIfGoingBackward += hc.POfThisIfGoingBackward #//WRONG, WRONG. DON'T EVEN BOTHER CHECKING IT, ITS WRONG
    hc.POfThisIfGoingForward += prev.POfThisIfGoingForward * hc.POfThisIfGoingForward#//JESUS, WTF
end

function linkWithThisNext(hc::HangingChance10, next::HangingChance10) # God i HOPE references work as they sauy they do ...
    push!(hc.nexts, next)
    push!(next.previouses, hc)
    next.POfThisIfGoingForward += hc.POfThisIfGoingForward #//WRONG, WRONG. DON'T EVEN BOTHER CHECKING IT, ITS WRONG
    hc.POfThisIfGoingBackward += next.POfThisIfGoingBackward * hc.POfThisIfGoingBackward#//JESUS, WTF
end

isThisStep(hc::HangingChance10, c::SyntaxProduct, index::int)::bool = (c == hc.chance && hc.indexInChance == index)

function makeNextOutOfThisWith(hc::HangingChance10, newObj::SyntaxInst, size::Int, marginalOfNewobjName::Real)::Union{HangingChance10, Nothing}
    # //next line finds needed HangingChance (**) in current it.involvedChances <<. 		//RIGHT NOW, THE ASSUMPTION IS THERES _ONLY_ _ONE_ .
    iter = filter((t->isThisStep(t, hc.chance, hc.indexInChance + 1)), newObj.involvedChances)
    @assert length(iter) < 2 "Should be only one needed HangingChance (**) in current it.involvedChances, not $(iter)"
    if length(iter) == 1
        if !(iter[1] in hc.nexts) linkWithThisNext(hc, iter[1]) end
        # //THERE IS ROOM FOR UPDATING currentPOfThisChanceToBeConsidered HERE
        # //UPDATE: this SHOULD be done inside linkWithThisNext. Dont trust it too much tho
        return nothing
    else
        temp = HangingChance10(hc.chance, newObj, hc.indexInChance + 1, size, hc.marginalOfChance, marginalOfNewobjName) #//,newobj.P * qualcosa??
        push!(newObj.involvedChances, temp)
        linkWithThisNext(hc, temp)
        # //THERE IS ROOM FOR UPDATING currentPOfThisChanceToBeConsidered HERE --
        #     //UPDATE: this SHOULD be done inside linkWithThisNext. Dont trust it too much tho
        return temp
    end
end


function makePrevOutOfThisWith(hc::HangingChance10, newObj::SyntaxInst, size::Int, marginalOfNewobjName::Real)::Union{HangingChance10, Nothing}
    # //next line finds needed HangingChance (**) in current it.involvedChances <<. 		//RIGHT NOW, THE ASSUMPTION IS THERES _ONLY_ _ONE_ .
    iter = filter((t->isThisStep(t, hc.chance, hc.indexInChance - 1)), newObj.involvedChances)
    @assert length(iter) < 2 "Should be only one needed HangingChance (**) in current it.involvedChances, not $(iter)"
    if length(iter) == 1
        if !(iter[1] in hc.previouses) linkWithThisPrevious(iter[1]) end
        # //THERE IS ROOM FOR UPDATING currentPOfThisChanceToBeConsidered HERE
        #     //UPDATE: this SHOULD be done inside linkWithThisPrevious. Dont trust it too much tho
        return nothing
    else
        temp = HangingChance10(hc.chance, newObj, hc.indexInChance - 1, size, hc.marginalOfChance, marginalOfNewobjName) #//,newobj.P * qualcosa??
        push!(newObj.involvedChances, temp)
        linkWithThisPrevious(hc, temp)
        # //THERE IS ROOM FOR UPDATING currentPOfThisChanceToBeConsidered HERE
        #     //UPDATE: this SHOULD be done inside linkWithThisPrevious. Dont trust it too much tho
        return temp
    end
end

function getOneLongFieldNext(hc:: HangingChance10, s::SyntaxCore)::Union{HangingChance10, Nothing}
    iter = filter((t->(t.length==1 && getName(t.object) ==s)), hc.nexts)
    return length(iter) == 0 ? nothing : iter[i]
end
function getOneLongFieldPrev(hc:: HangingChance10, s::SyntaxCore)::Union{HangingChance10, Nothing}
    iter = filter((t->(t.length==1 && getName(t.object) ==s)), hc.previouses)
    return length(iter) == 0 ? nothing : iter[i]
end


struct ChancesStructure10 # // dove chunkVector[i] è un temp il cui ULTIMO ELEMENTO è in i
						  #// MA SOPRATTUTTO, dove InsertAt[i] vuol dire che: finisce in i ESCLUSO, i.e. i è il _FROM_ _DEL_ _NEXT_.

    beginnings::Array{Array{HangingChance10}} # //the objs in [0] are: the ones whose _FROM_ _OF_ _NEXT_ , _i.e._ _ESCLUDED_ _TO_ is in 1. That is: when to_at(1)(meaning Excluded to) is searched, this is Shifted to [0].
    endings::Array{Array{HangingChance10}}  # the objs in [0] are: the ones where the FROM (of THIS, i.e. _TO_ _OF_ _PREV_) is at 0. That is, when you search from_at(1), this is Shifted to [0].
end

objsWhereFromOfNextShouldBe(cs::ChancesStructure10, i::Int)::Array{HangingChance10} = (i != 0) ? (cs.beginnings[i]) : (Array{HangingChance10}([])) #// Excluded, BUT UNCHECKED
objsWhereToOfPrevShouldBe(cs::ChancesStructure10, i::Int)::Array{HangingChance10} = (i != length(cs.endings)) ? (cs.endings[i+1]) : (Array{HangingChance10}([])) # //Excluded, BUT UNCHECKED

function reshape(cs::ChancesStructure10, from::Int, to::Int, howMuch::Int) #//to EXCLUDED
    if (howMuch < to - from)
        for i in from:(from + howMuch-1)
            cs.beginnings[i+1] = []
            cs.endings[i+1] = []
        end
        for i in to:(length(cs.beginnings)-1)
            for j in 0:(length(cs.beginnings[i+1])-1)
                if getFrom(cs.beginnings[i+1][j+1], i) < to cs.beginnings[i+1] = vcat(cs.beginnings[i+1][1:(j-1)], cs.beginnings[i+1][(j+1):end]) end
            end
        end
        cs.beginnings = vcat(cs.beginnings[1:(from + howMuch)], cs.beginnings[(to+1):end])
        for i in 0:(from-1)
            for j in 0:(length(cs.endings[i])-1)
                if getTo(cs.endings[i+1][j+1], i) >= from cs.endings[i+1] = vcat(cs.endings[i+1][1:(j-1)], cs.endings[i+1][j+1:end]) end
            end
        end
        cs.endings = vcat(cs.endings[1:(from + howMuch)], cs.endings[(to+1):end])
    else
        for i in from:(length(cs.beginnings)-1)
            for j in 0:(length(cs.beginnings[i+1])-1)
                if getFrom(cs.beginnings[i+1][j+1], i) < to cs.beginnings[i+1] = vcat(cs.beginnings[i+1][1:(j-1)], cs.beginnings[i+1][(j+1):end]) end
            end
        end
        tt = Array{Array{Array{HangingChance10}}}(undef,  howMuch - (to - from))
        for i in 1:size(tt)[1] tt[i] = [] end
        cs.beginnings = vcat(cs.beginnings[1:to], tt, cs.beginnings[(to+1):end])
        for i in 0:(to-1)
            for j in 0:(length(cs.endings[i])-1)
                if getTo(cs.endings[i+1][j+1], i) >= from cs.endings[i+1] = vcat(cs.endings[i+1][1:(j-1)], cs.endings[i+1][j+1:end]) end
            end
        end
        tt = Array{Array{Array{HangingChance10}}}(undef,  howMuch - (to - from))
        for i in 1:size(tt)[1] tt[i] = [] end
        cs.endings = vcat(cs.endings[1:to], tt, cs.endings[(to+1):end])
    end
end

function addBeginning(cs::ChancesStructure10, temp::HangingChance10, fromOfNext::Int)
    push!(cs.beginnings[fromOfNext - 1], temp)
end
function addEnding(cs::ChancesStructure10, temp::HangingChance10, fromOfThis::Int)
    push!(cs.endings[fromOfThis], temp)
end
