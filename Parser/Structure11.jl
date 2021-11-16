include("StackOfChances.jl")
include("FinishedsStructure10.jl")
include("PosteriorsStructure.jl")
include("BidirectionalChancesStructure11.jl")

#include"ScopedTypeInference.h"

struct ScopedTypeInference #//Boi: this class, will GROW............
# //note 1: this is the Wrong way to handle sum types
# //note 2: yeah, a MATRIX will happen here!!
# //note 3: this class might become a DAC !!!
	allDefinitions::Array{Tuple{String, TermTag}}
end
ScopedTypeInference() = ScopedTypeInference([])
function can_be_a(request::TermTag, chance::TermTag)::Bool
    if (request === chance) return true
    elseif request isa TSumTag
        for c in request.data
            if can_be_a(c, chance) return true end
        end
    end
    return false
end


mutable struct Structure11
	finisheds::FinishedsStructure10
	hangings::ChancesStructure10
	stack::StackOfChances
	scopedTypeInference::ScopedTypeInference
    inputVec::Array{String}
    posteriorsStructure::PosteriorsStructure
end

Structure11() = Structure11(FinishedsStructure10(), ChancesStructure10(), StackOfChances(), ScopedTypeInference(), [], PosteriorsStructure())


size(S::Structure11) = size(S.finisheds)
trace(S::Structure11) = trace(S.finisheds)
function reshape(S::Structure11, from::Int, to::Int, howMuch::Int)
    reshape(S.hangings, from, to, howMuch);
    reshape(S.finisheds, from, to, howMuch);
end


function makeNewNextFromSynt(hc_prev::HangingChance10, newObj::SyntaxInstOwner, size::Int, marginalOfNewobjName::Real)::HangingChance10
    new_hc = HangingChance10(hc_prev.chance, newObj.s, hc_prev.indexInChance + 1, size, hc_prev.marginalOfChance, marginalOfNewobjName) #//,newobj.P * qualcosa??
    linkWithThisNext!(hc_prev, new_hc)
    # //THERE IS ROOM FOR UPDATING currentPOfThisChanceToBeConsidered HERE --
    #     //UPDATE: this SHOULD be done inside linkWithThisNext!. Dont trust it too much tho
    return new_hc
end
function makeNewPrevFromSynt(hc_next::HangingChance10, newObj::SyntaxInstOwner, size::Int, marginalOfNewobjName::Real)::HangingChance10
    new_hc = HangingChance10(hc_next.chance, newObj.s, hc_next.indexInChance - 1, size, hc_next.marginalOfChance, marginalOfNewobjName) #//,newobj.P * qualcosa??
    linkWithThisPrevious!(hc_next, new_hc)
    # //THERE IS ROOM FOR UPDATING currentPOfThisChanceToBeConsidered HERE
    #     //UPDATE: this SHOULD be done inside linkWithThisPrevious!. Dont trust it too much tho
    return new_hc
end
function makeObjfoundAsChance_goingForward(S::Structure11, what_field::SyntaxField, objectFound::SyntaxInstObject, hChance::HangingChance10, objfound_from::Int, objfound_to::Int, PMarginal::Real)
    temp1 = SyntaxInstField(what_field, objectFound, 0.5)
    # //first comment: LOL, you HERE is where computing the P GETS SERIOUS.......
    # //second comment: Note the nice symmetry with below.
    temp2 = SyntaxInstOwner(temp1) # Useless, i'd say
    add(S.finisheds, objfound_from, objfound_to, temp2) # //u are goddam right, it DOESNT go into the stack //i see we all agree on this rn
    temp3 = makeNewNextFromSynt(hChance, temp2, objfound_to - objfound_from, PMarginal) #  // well, i THINK it's co???
    temp3
end
function makeObjfoundAsChance_goingBackward(S::Structure11, what_field::SyntaxField, objectFound::SyntaxInstObject, hChance::HangingChance10, objfound_from::Int, objfound_to::Int, PMarginal::Real)
    temp1 = SyntaxInstField(what_field, objectFound, 0.5)
    # //first comment: LOL, you HERE is where computing the P GETS SERIOUS.......
    # //second comment: Note the nice symmetry with below.
    temp2 = SyntaxInstOwner(temp1) # Useless, i'd say
    temp3 = makeNewPrevFromSynt(hChance, temp2, objfound_to - objfound_from, PMarginal) #  // well, i THINK it's co???
    add(S.finisheds, objfound_from, objfound_to, temp2) # //u are goddam right, it DOESNT go into the stack //i see we all agree on this rn
    temp3
end
function makeReferenceChance_goingForward(S::Structure11, what_field::SyntaxField, chance::StackableChance)
    # // do i need th second check? Actually: What does it even do, i wonder?
    temp1 = SyntaxInstReference(getType(what_field), S.inputVec[chance.to+1], 0.5)
    # //first comment: LOL, you HERE is where computing the P GETS SERIOUS.......
    temp2 = SyntaxInstField(what_field, temp1, 0.5)
    # //second comment: possibly even more serious
    temp4 = SyntaxInstOwner(temp2)
    temp5 = makeNewNextFromSynt(chance.what, temp4, 1, getMarginal(S.posteriorsStructure, what_field))
    # //wait.. But what good does temp->prob even do here then^^
    add(S.finisheds, chance.to, chance.to + 1, temp4)
    # //not only this does not go into the stack(as an AlreadyFinished)-- I DON'T WANT TO PUT IT INTO THE FINISHED EITHER..... //
    temp5
end
function makeReferenceChance_goingBackward(S::Structure11, what_field::SyntaxField, chance::StackableChance)
    # // do i need th second check? Actually: What does it even do, i wonder?
    temp1 = SyntaxInstReference(getType(what_field), S.inputVec[chance.from], 0.5)
    # //first comment: LOL, you HERE is where computing the P GETS SERIOUS.......
    temp2 = SyntaxInstField(what_field, temp1, 0.5)
    # //second comment: possibly even more serious
    temp4 = SyntaxInstOwner(temp2)
    temp5 = makeNewPrevFromSynt(chance.what, temp4, 1, getMarginal(S.posteriorsStructure, what_field))
    # //wait.. But what good does temp->prob even do here then^^
    add(S.finisheds, chance.from - 1, chance.from, temp4)
    # //not only this does not go into the stack(as an AlreadyFinished)-- I DON'T WANT TO PUT IT INTO THE FINISHED EITHER..... //
    temp5
end


function processObjectFound(S::Structure11, chanceF::StackableObject)
    obj::SyntaxInstObject = chanceF.whatObject
    println( "having object: " , obj.name|>trace , " at " , chanceF.from , "-" , chanceF.to - 1 , " (included)")
    # margOfObjName::Real = getP(obj.name) # //JESUS, WHAT A FUCKING MESS.............................................

    presentProductChances_goingBack = chancesNeedingThisPreviously_obj(S.hangings, chanceF.to, chanceF.whatObject)
    presentProductChances_goingForward = chancesNeedingThisNext_obj(S.hangings, chanceF.from, chanceF.whatObject)
    for (hc_prev, needed_field) in presentProductChances_goingForward
        new_created_hc = makeObjfoundAsChance_goingForward(S, needed_field, chanceF.whatObject, hc_prev, chanceF.from, chanceF.to, getMarginal(S.posteriorsStructure, needed_field))
        insert!(S.stack, new_created_hc.POfThisIfGoingForward, StackableChance(new_created_hc ,chanceF.from,chanceF.to, true, false)) # //wait.. But what good does temp->prob even do here then
        addEnding(S.hangings, new_created_hc, chanceF.to)
    end
    for (hc_next, needed_field) in presentProductChances_goingBack
        new_created_hc = makeObjfoundAsChance_goingBackward(S, needed_field, chanceF.whatObject, hc_next, chanceF.from, chanceF.to, getMarginal(S.posteriorsStructure, needed_field))
        insert!(S.stack, new_created_hc.POfThisIfGoingForward, StackableChance(new_created_hc ,chanceF.from,chanceF.to, false, true ))  #wait.. But what good does temp->prob even do here then
        addBeginning(S.hangings, new_created_hc, chanceF.from)
    end
end

function processFinishedSyntax(S::Structure11, chanceF::StackableFinishedSyntax)
    obj::SyntaxInstOwner = chanceF.whatFinished
    println( "having synt: " , obj|>getName|>getString , " at " , chanceF.from , "-" , chanceF.to - 1 , " (included)")

    for x in at(S.finisheds, chanceF.from, chanceF.to)
        if deepEqual(obj.s, x.s)
            # throw(DomainError("OK THIS ACTUALLY ACTUALLY HAPPENEDDDD: $(obj.s|>trace),     $(x.s|>trace)"))
            return
        end
    end
    # //^ THE IDEA WAS _EXACTLY_ NOT TO HAVE TO DO THIS ...............................................................

    margOfObjName = getMarginal(S.posteriorsStructure, getName(obj)) # //JESUS, WHAT A FUCKING MESS.............................................

    presentProductChances_goingForward = chancesNeedingThisNext(S.hangings, chanceF.from, chanceF.whatFinished)
    presentProductChances_goingBack = chancesNeedingThisPreviously(S.hangings, chanceF.to, chanceF.whatFinished)

    allSyntProds = getAllSyntaxProductsWithIndexFor(S.posteriorsStructure, getName(obj))
    for synt_with_index::SomeChancewIndex{SyntaxProduct} in allSyntProds
        new_hc = HangingChance10(synt_with_index.chance, obj.s, synt_with_index.index, chanceF.to - chanceF.from, synt_with_index.P, margOfObjName)
        insert!(S.stack, new_hc.POfThisIfGoingForward + new_hc.POfThisIfGoingBackward, StackableChance(new_hc, chanceF.from, chanceF.to, true, true))
        addBeginning(S.hangings, new_hc, chanceF.from)
        addEnding(S.hangings, new_hc, chanceF.to)

        linked_to_anything = false # How to make this cleaner ?
        # Even more importantly: Are you SURE that ANY hc_bw or hc_fw WILL be triggered here in this loop, at some SyntaxProduct ?
        for hc_prev::HangingChance10 in presentProductChances_goingForward
            if hc_prev.chance == new_hc.chance && hc_prev.indexInChance + 1 == new_hc.indexInChance
                linkWithThisPrevious!(new_hc, hc_prev)
                linked_to_anything = true
            end
        end
        for hc_next::HangingChance10 in presentProductChances_goingBack
            if hc_next.chance == new_hc.chance && hc_next.indexInChance - 1 == new_hc.indexInChance
                linkWithThisNext!(new_hc, hc_next)
                linked_to_anything = true
            end
        end
        if linked_to_anything
            for foundFinished::SizeWBounds in getAllFinalObjsLinked(new_hc, chanceF.from, chanceF.to)
                insert!(S.stack, getP(foundFinished.s), StackableFinishedSyntax(SyntaxInstOwner(foundFinished.s), foundFinished.from, foundFinished.to))
            end
        end
    end

    for thingy::SomeChancewIndex{SyntaxChoice} in getAllSyntaxChoicesWithIndexFor(S.posteriorsStructure, getName(obj))
        # //THIS IS IMPORTANT:
        actualP::Real = thingy.P * getP(chanceF)

        temp1 = SyntaxInstOwner(SyntaxInstChoice(thingy.chance, thingy.index, obj.s, actualP))
        temp2 = StackableFinishedSyntax(temp1, chanceF.from, chanceF.to)
        pp = getP(temp2)
        insert!(S.stack, pp, temp2)
    end

    for thingy::someOtherReturn in getAllSyntaxBindingsFor(S.posteriorsStructure, getName(obj))
        temp1 = SyntaxInstObject(gettypeThatHasSynt(thingy), obj.s, thingy.P)
        insert!(S.stack, getP(temp1), StackableObject(temp1, chanceF.from, chanceF.to))
        add(S.finisheds, chanceF.from, chanceF.to, SyntaxInstOwner(temp1))  #//to EXCLUDED,
    end
    add(S.finisheds, chanceF.from, chanceF.to, obj) # //to EXCLUDED
end



function processChance(S::Structure11, chance::StackableChance)

    linkedWithAnything = false
    if (chance.goForward && hasEnded(chance.what)) || (chance.goBackward && hasJustBegun(chance.what))
         linkedWithAnything = true
    end

    if (chance.goForward && !hasEnded(chance.what) && chance.to < size(S))
        for hc_next in chancesNeedingThisPreviously_hc(S.hangings, chance.to, chance.what)
            linkWithThisNext!(chance.what, hc_next)
            linkedWithAnything = true
        end
        # //careful here: # USE A WORD AS A VARIABLE:
        for possibleNeeded in getWhatNeedsNext(chance.what)
            if possibleNeeded isa SyntaxField && getOneLongFieldNext(chance.what, possibleNeeded)===nothing && !occursin(S.inputVec[chance.to+1], "()[]-><{}:=.,;:") # TODO: is this right? Or should be ! ?
                if !any(chance.what.nexts .|> (x->x.chance == possibleNeeded && x.object.objectFound isa SyntaxInstReference && x.object.objectFound.text == S.inputVec[chance.to+1]))
                    new_ref_field = makeReferenceChance_goingForward(S, possibleNeeded, chance)
                    insert!(S.stack, new_ref_field.POfThisIfGoingForward, StackableChance(new_ref_field ,chance.to,chance.to + 1, true, false))
                    addEnding(S.hangings, new_ref_field, chance.to+1)
                    # NO: linkedWithAnything = true
                end
            end
        end
    end

    if chance.goBackward && !hasJustBegun(chance.what) && chance.from > 0
        for hc_prev in chancesNeedingThisNext_hc(S.hangings, chance.from, chance.what)
            linkWithThisPrevious!(chance.what, hc_prev)
            linkedWithAnything = true
        end
        # //careful here: # USE A WORD AS A VARIABLE:
        for possibleNeeded in getWhatNeedsBefore(chance.what)
            if possibleNeeded isa SyntaxField && getOneLongFieldPrev(chance.what, possibleNeeded) ===nothing && !occursin(S.inputVec[chance.from], "()[]-><{}:=.,;:") # chance.from -1, +1 cuz Julia
                if !any(chance.what.previouses .|> (x->x.chance == possibleNeeded && x.object.objectFound isa SyntaxInstReference && x.object.objectFound.text == S.inputVec[chance.from]))
                    new_ref_field = makeReferenceChance_goingBackward(S, possibleNeeded, chance)
                    insert!(S.stack, new_ref_field.POfThisIfGoingBackward, StackableChance(new_ref_field, chance.from - 1, chance.from, false, true))
                    addBeginning(S.hangings, new_ref_field, chance.from-1)
                    # NO: linkedWithAnything = true
                end
            end
            # // else{ something different, if you would ever need the bASICsTING}
        end
    end

    if linkedWithAnything
        for foundFinished::SizeWBounds in getAllFinalObjsLinked(chance.what, chance.from, chance.to)
            insert!(S.stack, getP(foundFinished.s), StackableFinishedSyntax(SyntaxInstOwner(foundFinished.s), foundFinished.from, foundFinished.to))
        end
    end
end

getBestTotalFound(S::Structure11) = getBestTotalFound(S.finisheds)

function insertTerminal(S::Structure11, from::Int, to::Int, what::SyntaxTerm, P::Real)
    temp1 = SyntaxInstOwner(SyntaxInstTerm(what, P))
    temp2 = StackableFinishedSyntax(temp1, from,to)
    if size(S) < to
        ss = size(S)
        reshape(S.finisheds, ss, ss, to-ss)
        reshape(S.hangings, ss, ss, to-ss)
    end
    insert!(S.stack, P, temp2)
end


process_(S::Structure11, t::StackableChance) = processChance(S, t)
process_(S::Structure11, t::StackableFinishedSyntax) = processFinishedSyntax(S, t)
process_(S::Structure11, t::StackableObject) = processObjectFound(S, t)

printt(s::StackableChance) = "$(s.from) to $(s.to): Chance for $(getString(s.what.chance)), current: $(trace(s.what.object))"
printt(s::StackableFinishedSyntax) = "$(s.from) to $(s.to): Finished $(trace(s.whatFinished.s))"
printt(s::StackableObject) = "$(s.from) to $(s.to): Found: $(trace(s.whatObject.syntax))"
# chance|>printt
#S.stack.stack|>length
# S.stack.stack[1][2]|>printt
# S.stack.stack[2][2]|>printt
# S.stack.stack[3][2]|>printt

function doTheBestYouCan(S::Structure11)
    goOn = true
    while goOn
        # if (0 == 1)//stack.peekBestScore() < posteriorsStructure.epsilon)
        #     goOn = false
        #     continue
        # end
        chance = getBest!(S.stack)
        if chance !== nothing
            process_(S, chance)
            if chance.from == 0 && chance.to == size(S) goOn = false end
        else goOn = false
        end
    end
end
