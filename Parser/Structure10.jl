include("StackOfChances.jl")
include("FinishedsStructure10.jl")
# include("PosteriorsStructure.jl")
include("BidirectionalChancesStructure10.jl")

#include"ScopedTypeInference.h"
struct Structure10
	finisheds::FinishedsStructure10
	hangings::ChancesStructure10
	stack::StackOfChances
	scopedTypeInference::ScopedTypeInference
    inputVec::Array{String}

	# //use this: stack.insert(obj->getP(), sSyntaxInstObjectNamedtd::move(obj));
	# //and this: addFinished(from, to, std::move(SyntaxInst{ std::make_unique<SyntaxInstTerm>(chance, posteriorsStructure.getMarginal(chance)) }));
end


size(S::Structure10) = size(S.finisheds)
trace(S::Structure10) = trace(S.finisheds)
function reshape(S::Structure10, from::Int, to::Int, howMuch::Int)
    reshape(S.hangings, from, to, howMuch);
    reshape(S.finisheds, from, to, howMuch);
end


function processObjectFound(S::Structure10, chanceF::StackableObject)
    obj::SyntaxInstObject = chanceF.whatObject
    println( "having object: " , obj|>getType|>trace , " at " , chanceF.from , "-" , chanceF.to - 1 , " (included)")

    # //auto& v = finisheds.at(chanceF.from, chanceF.to);
    # //if (std::any_of(v.begin(), v.end(), [&obj](auto& t) {return obj.deepEqual(t.getPointer()); })) { return; }
    # //^ THE IDEA WAS _EXACTLY_ NOT TO HAVE TO DO THIS ...............................................................

    margOfObjName::Real = getP(obj) # //JESUS, WHAT A FUCKING MESS.............................................

    allPotentialPreviouses = objsWhereFromOfNextShouldBe(S.hangings, chanceF.from)
    for thingy::HangingChance10 in allPotentialPreviouses
        for possibleNeeded in getWhatNeedNext(thingy)
            # // here, ALL TEMPORARYNESS HAS BEEN DOWNLOADED INTO S.scopedTypeInference.can_be_a() ...... THINK ABOUT THIS BOI!!!!
            if possibleNeeded isa SyntaxField && can_be_a(S.scopedTypeInference, getType(possibleNeeded), getType(obj))
                forward_addObjfoundAsChance(S, possibleNeeded, obj, thingy, chanceF.from, chanceF.to, getMarginal(S.posteriorsStructure, possibleNeeded))
            end
        end
    end
    # //idem^
    for thingy::HangingChance10 in objsWhereToOfPrevShouldBe(S.hangings, chanceF.to)
        for possibleNeeded in getWhatNeedBefore(thingy)
            # // here, ALL TEMPORARYNESS HAS BEEN DOWNLOADED INTO S.scopedTypeInference.can_be_a() ...... THINK ABOUT THIS BOI!!!!
            if possibleNeeded isa SyntaxField && can_be_a(scopedTypeInference, getType(possibleNeeded), getType(obj))
                backward_addObjfoundAsChance(S, possibleNeeded, obj, thingy, chanceF.from, chanceF.to, getMarginal(S.posteriorsStructure, possibleNeeded))
            end
        end
    end
end

function processFinishedSyntax(S::Structure10, chanceF::StackableFinishedSyntax)
    obj::SyntaxInst = chanceF.whatFinished
    println( "having synt: " , obj|>getName|>getString , " at " , chanceF.from , "-" , chanceF.to - 1 , " (included)")

    if at(S.finisheds, chanceF.from, chanceF.to) .|> (x->deepEqual(obj, x)) |> any return end
    # //^ THE IDEA WAS _EXACTLY_ NOT TO HAVE TO DO THIS ...............................................................

    margOfObjName = getMarginal(S.posteriorsStructure, obj.getName()) # //JESUS, WHAT A FUCKING MESS.............................................

    createdProductChances = Array{HangingChance10}([])

    allPotentialPreviouses = objsWhereFromOfNextShouldBe(S.hangings, chanceF.from)
    for thingy::HangingChance10 in allPotentialPreviouses
        if needsNext(thingy, getName(obj)) #//there ARE _IS_ _A_ _ISSUES_ here.....
            temp = makeNextOutOfThisWith(thingy, obj, chanceF.to - chanceF.from, margOfObjName)
            if (temp!==nothing) push!(createdProductChances, temp) end
        end
    end
    # //idem^
    allPotentialNexts = objsWhereToOfPrevShouldBe(S.hangings, chanceF.to)
    for thingy::HangingChance10 in allPotentialNexts
        if needsBefore(thingy, getName(obj)) # //there ARE _IS_ _A_ _ISSUES_ here.....
            temp = makePrevOutOfThisWith(thingy, obj, chanceF.to - chanceF.from, margOfObjName)
            if (temp!==nothing) push!(createdProductChances, temp) end
        end
    end

    for thingy::SomeChancewIndex{SyntaxProduct} in getAllSyntaxProductsWithIndexFor(S.posteriorsStructure, getName(obj))
        iter = filter(t->isThisStep(t, thingy.chance, thingy.index), obj.involvedChances)
        if (iter == obj.involvedChances.end())
            push!(createdProductChances, HangingChance10(thingy.chance, obj, thingy.index, chanceF.to - chanceF.from, getP(thingy), margOfObjName))
            push!(obj.involvedChances, createdProductChances[end])
        end
    end

    for thingy::HangingChance10 in createdProductChances #//the prev 3 steps go here
        insert!(S.stack, thingy.POfThisIfGoingForward + thingy.POfThisIfGoingBackward, StackableChance(thingy, chanceF.from, chanceF.to, true, true))
    end

    for thingy::SomeChancewIndex{SyntaxChoice} in getAllSyntaxChoicesWithIndexFor(S.posteriorsStructurem, getName(obj))
        # //THIS IS IMPORTANT:
        actualP::Real = getP(thingy) * getP(chanceF)

        temp1 = SyntaxInstChoice(thingy.chance, thingy.index, obj, actualP)
        temp2 = StackableFinishedSyntax(temp1, chanceF.from, chanceF.to)
        pp = getP(temp2)
        insert!(S.stack, pp, temp2)
    end

    for thingy::someOtherReturn in getAllSyntaxBindingsFor(S.posteriorsStructure, getName(obj))
        temp1 = SyntaxInstObject(gettypeThatHasSynt(thingy), obj, getP(thingy))

        # //here, you MIGHT WANT TO DO THIS:
        temp2 = StackableObject(temp1, chanceF.from, chanceF.to)
        pp = getP(temp2)
        insert!(S.stack, pp, temp2)

        # //Except, i'm SKIPPING PROPAGATING FINISHED TYPES as for now, too see what happens- SO::
        # //what you get is,
        # //finisheds.add(chanceF.from, chanceF.to, SyntaxInst{ std::move(temp1) });//to EXCLUDED,
        # // ^^ - NOT.
    end
    add(S.finisheds, chanceF.from, chanceF.to, obj) # //to EXCLUDED
end

function forward_addObjfoundAsChance(S::Structure10, what_field::SyntaxField, objectFound::SyntaxInstObject, hChance::HangingChance10, objfound_from::Int, objfound_to::Int, PMarginal::Real)
    temp1 = SyntaxInstField(what_field, objectFound, 0.5)
    # //first comment: LOL, you HERE is where computing the P GETS SERIOUS.......
    # //second comment: Note the nice symmetry with below.
    temp2 = SyntaxInst(temp1) # Useless, i'd say
    temp3 = makeNextOutOfThisWith(hChance, temp2, objfound_to - objfound_from, PMarginal) #  // well, i THINK it's co???
    if temp3!==nothing insert!(S.stack, temp3.POfThisIfGoingForward, StackableChance(temp3 ,objfound_from,objfound_to, true, false)) end # //wait.. But what good does temp->prob even do here then
    add(S.finisheds, objfound_from, objfound_to, temp2) # //u are goddam right, it DOESNT go into the stack //i see we all agree on this rn
end

function backward_addObjfoundAsChance(S::Structure10, what_field::SyntaxField, objectFound::SyntaxInstObject, hChance::HangingChance10, objfound_from::Int, objfound_to::Int, PMarginal::Real)
    temp1 = SyntaxInstField(what_field, objectFound, 0.5)
    # //first comment: LOL, you HERE is where computing the P GETS SERIOUS.......
    # //second comment: Note the nice symmetry with below.
    temp2 = SyntaxInst(temp1) # Useless, i'd say
    temp3 = makeNextOutOfThisWith(hChance, temp2, objfound_to - objfound_from, PMarginal) #  // well, i THINK it's co???
    if temp3!==nothing insert!(S.stack, temp3.POfThisIfGoingForward, StackableChance(temp3 ,objfound_from,objfound_to, false, true )) end #wait.. But what good does temp->prob even do here then
    add(S.finisheds, objfound_from, objfound_to, temp2) # //u are goddam right, it DOESNT go into the stack //i see we all agree on this rn
end

function processChance(S::Structure10, chance::StackableChance)
    addBeginning(S.hangings, chance.what, chance.to)
    addEnding(S.hangings, chance.what, chance.from)
    if (chance.goForward && !hasEnded(chance.what) && chance.to < size(S))
        for (it, to_) in EverythingBeginningAt(S.finisheds, chance.to)
            # idea: it::SyntaxInst, but it was wrapped in a IterableForElementsStartingFrom/ CustomIterForward that had a getTo() method...
            if needsNext(chance.what, getName(it)) #//COULD BE SLIGTHY FASTER (but uglier)  //maybe there are still _IS_ _A_ issues here ?
                # //ponder on the fact that if you are here, it's prolly
                # //NOT ??
                # //for an Identifier OR SIMILAR-- that is, OR AN SyntaxInstField
                temp = makeNextOutOfThisWith(chance.what, it, to_ - chance.to, getMarginal(S.posteriorsStructure, getName(it)))
                if (temp!==nothing) insert!(S.stack, temp.POfThisIfGoingForward, StackableChance(temp, chance.to, to_, true, false)) end  #//wait.. But what good does temp->prob even do here then
            # //I'M CURRENLY(dec 2019) TRYING THE VERSION WHERE I DON'T NEED THIS:
            # else # //THE else MEANS I'M ASSUMING A BINDED SYNTAX WILL NEVER BE IN ANOTHER SYNTAX (think about it), FOR SOME REASON
            end
                for possibleNeeded in getWhatNeedNext(chance.what)
                    if possibleNeeded isa SyntaxField
                        pn = possibleNeeded
                        # //OH MY GOD... JESUS THIS IS AWFUL, WTF
                        for objectFound::Temp_Type in getBindings(S.posteriorsStructure, getName(it))
                            # // here, ALL TEMPORARYNESS HAS BEEN DOWNLOADED INTO scopedTypeInference.can_be_a() ...... THINK ABOUT THIS BOI!!!!
                            if can_be_a(scopedTypeInference, getType(pn), objectFound)
                                sio = SyntaxInstObject(objectFound, it, 1.0)  #  //LOL it LITERALLY says 1.0
                                forward_addObjfoundAsChance(S, pn, sio, chance.what, chance.to, to_, getMarginal(S.posteriorsStructure, possibleNeeded))
                            end
                        end
                    end
                end
            # end
        end

        # //careful here:
        for possibleNeeded in getWhatNeedNext(chance.what)
            if possibleNeeded isa SyntaxField && getOneLongFieldNext(!chance.what, possibleNeeded)===nothing # TODO: is this right? Or should be ! ?
                # // do i need th second check? Actually: What does it even do, i wonder?
                temp1 = SyntaxInstReference(getType(possibleNeeded), S.inputVec[chance.to+1], 0.5)
                # //first comment: LOL, you HERE is where computing the P GETS SERIOUS.......
                temp2 = SyntaxInstField(possibleNeeded, temp1, 0.5)
                # //second comment: possibly even more serious
                temp5 = makeNextOutOfThisWith(chance.what, temp2, 1, getMarginal(S.posteriorsStructure, possibleNeeded))

                if (temp5!==nothing) insert!(S.stack, temp5.POfThisIfGoingForward, StackableChance(temp5 ,chance.to,chance.to + 1, true, false)) end
                # //wait.. But what good does temp->prob even do here then^^
                add(S.finisheds, chance.to, chance.to + 1, temp2)
                # //not only this does not go into the stack(as an AlreadyFinished)-- I DON'T WANT TO PUT IT INTO THE FINISHED EITHER..... //
            # // else{ something different, if you would ever need the bASICsTING}
            end
        end
    elseif hasEnded(chance.what)
        for b in getFinalObjsFromEnd(chance.what)
            insert!(S.stack, getP(b[2]), StackableFinishedSyntax(b[2], chance.to - b[1], chance.to))
        end
    end

    if chance.goBackward && !hasJustBegun(chance.what) && chance.from > 0
        for (it, from_) in EverythingEndingAt(S.finisheds, chance.from)
            # idea: it::SyntaxInst, but it was wrapped in a IterableForElementsWhatev/ CustomIterBack that had a getTo() method...
            if needsBefore(chance.what, getName(it)) #//COULD BE SLIGTHY FASTER (but uglier)   //maybe there are still _IS_ _A_ issues here ?
                # //ponder on the fact that if you are here, it's prolly
                # //NOT ??
                # //for an Identifier OR SIMILAR-- that is, OR AN SyntaxInstField
                temp = makePrevOutOfThisWith(chance.what, it, chance.from - from_, getMarginal(posteriorsStructure, getName(it)))
                if (temp!==nothing) insert!(S.stack, temp.POfThisIfGoingBackward, StackableChance(temp , from_,chance.from, false, true)) end # //wait.. But what good does temp->prob even do here the
            # else //THE else MEANS I'M ASSUMING A BINDED SYNTAX WILL NEVER BE IN ANOTHER SYNTAX (think about it), FOR SOME REASON
            end
                for possibleNeeded in getWhatNeedBefore(chance.what)
                    if possibleNeeded isa SyntaxField
                        pn = possibleNeeded
                        # //OH MY GOD... JESUS THIS IS AWFUL, WTF
                        for objectFound::Temp_Type in getBindings(S.posteriorsStructure, getName(it))
                            # // here, ALL TEMPORARYNESS HAS BEEN DOWNLOADED INTO scopedTypeInference.can_be_a() ...... THINK ABOUT THIS BOI!!!!
                            if can_be_a(S.scopedTypeInference, getType(pn), objectFound)
                                sio = SyntaxInstObject(bjectFound, it, 1.0 )# //LOL it LITERALLY says 1.0
                                backward_addObjfoundAsChance(S, pn, sio, chance.what, from_, chance.from, getMarginal(S.posteriorsStructure, possibleNeeded))
                            end
                        end
                    end
                end
            # end
        end
        # //careful here:
        # //if (finisheds.at(chance.from - 1, chance.from).empty() || !std::holds_alternative<std::unique_ptr<SyntaxInstTerm>>(finisheds.at(chance.from - 1, chance.from).front().get()))//temporary, rn should be fine tho
        # //{
        for possibleNeeded in getWhatNeedBefore(chance.what)
            if possibleNeeded isa SyntaxField && getOneLongFieldNext(chance.what, possibleNeeded) ===nothing
                # // do i need th second check? Actually: What does it even do, i wonder?
                temp0 = possibleNeeded
                temp1 = SyntaxInstReference(getType(temp0), S.inputVec[chance.from], 0.5)
                # //first comment: LOL, you HERE is where computing the P GETS SERIOUS.......
                temp2 = SyntaxInstField(temp0, temp1, 0.5)
                # //second comment: possibly even more serious
                temp4 = temp2
                temp5 = makePrevOutOfThisWith(chance.what, temp4, 1, posteriorsStructure.getMarginal(possibleNeeded))
                if (temp5 !== nothing) insert!(S.stack, temp5.POfThisIfGoingBackward, StackableChance(temp5, chance.from - 1, chance.from, false, true)) end
                # //wait.. But what good does temp->prob even do here then^^
                add(S.finisheds, chance.from - 1, chance.from, temp4)
                # //not only this does not go into the stack(as an AlreadyFinished)-- I DON'T WANT TO PUT IT INTO THE FINISHED EITHER..... //
            end
            # // else{ something different, if you would ever need the bASICsTING}
        end
    elseif hasJustBegun(chance.what)
        for b in getFinalObjsFromStart(chance.what)
            stack.insert(getP(b[2]), StackableFinishedSyntax(b[2], chance.from, chance.from + b[1]))
        end
    end
end

getBestTotalFound(S::Structure10) = getBestTotalFound(S.finisheds)

function insertTerminal(S::Structure10, from::Int, to::Int, what::SyntaxTerm, P::Real)
    temp1 = SyntaxInstTerm(what, P)
    temp2 = StackableFinishedSyntax(temp1, from,to)
    insert!(S.stack, P, StackableBoid(temp2))
end


process_(S::Structure10, t::StackableChance) = processChance(S, t)
process_(S::Structure10, t::StackableFinishedSyntax) = processFinishedSyntax(S, t)
process_(S::Structure10, t::StackableObject) = processObjectFound(S, t)

function doTheBestYouCan(S::Structure10)
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
