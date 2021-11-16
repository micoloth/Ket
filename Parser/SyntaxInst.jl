
include("Syntaxes.jl")
# it REQUIRES that you included ("mylambda1_tag.jl") at Some Point!!!

abstract type SyntaxInst end
abstract type Accepted_SynatxInst_type <: SyntaxInst end
# ^ SyntaxInstObject, SyntaxInstReference, SyntaxInstNativeString <: Accepted_SynatxInst_type;
abstract type SyntaxInstProduct <: SyntaxInst end

wouldFit(si::SyntaxInst, s::SyntaxCore)::Bool = si.name == s
getName(s::SyntaxInst) = s.name

struct SyntaxInstTerm <: SyntaxInst
    name::SyntaxTerm
	P::Real  # //I might be wrong, but this is just the marginal
end

mutable struct SyntaxInstReference <: Accepted_SynatxInst_type
    # //it's a variable.
    # //note: the name of a Term is the USE OF A GLOBALLY DEFINED VARIABLE # (Will i have to fix this?)
    # //note: a variable definition CONTAINS A VARIABLE (i.e., the name.)
	type::TermTag # //it contains THE TYPE OF THE VAR YOU ARE JUST REFERENCING
	text::String #
	P::Real # //What is this, really? I contains the likelyhood of type being represented by a free variable, and the similarity of the sentence maybe?
    inferred_obj::Union{Nothing, TAnnoTag, Error} # This HAS BEEN BUIT UP ALREADY. BUT, it still has Holes ot Type variables ofc!! Also: it CAN be an Errored one!!
end
SyntaxInstReference(type, text, P) = SyntaxInstReference(type, text, P, nothing)

mutable struct SyntaxInstNativeString <: Accepted_SynatxInst_type
    # //it's a string
	text::String
	P::Real # //What is this, really? Prob a constant? Or >>1<<?
    inferred_obj::Union{Nothing, TAnnoTag, Error} # This HAS BEEN BUIT UP ALREADY. BUT, it still has Holes ot Type variables ofc!! Also: it CAN be an Errored one!!
end
SyntaxInstNativeString(text, P) = SyntaxInstNativeString(text, P, nothing)

mutable struct SyntaxInstObject <: Accepted_SynatxInst_type
    # //a syntax that results in a obj
    name::TermTag # This is THE TYPE OF THE OBJ YOU JUST FOUND
    syntax::SyntaxInst  # //it is THE SYNTAX THAT OBJECT IS USING
    PofObjectAndBelowGivenBelow::Real #//it's the P of the fact that syntax meant object, times P of syntax and stuff.
    inferred_obj::Union{Nothing, TAnnoTag, Error} # This HAS BEEN BUIT UP ALREADY. BUT, it still has Holes ot Type variables ofc!! Also: it CAN be an Errored one!!
end
SyntaxInstObject(name, syntax, PofObjectAndBelowGivenBelow) = SyntaxInstObject(name, syntax, PofObjectAndBelowGivenBelow, nothing)

# //note: i'm doing so that now, same SyntaxInst form with two different >FIELD >NAMES are different SyntaxInstCores.
# //		AT THIS POINT I BASICALLY HAVE NO IDEA WHAT I'M DOING
struct SyntaxInstField <: SyntaxInst
	name::SyntaxField  #  //it contains THE NAME OF THE FIELD this goes into, AND also the TYPE of the object REQUIRED
	objectFound::Accepted_SynatxInst_type
	# //note that, there is No duplicate informations, because of __IS_A__<<.
	# //there Could be incoherencies tho.
	PofThisAndBelowGivenBelow::Real  #  //posterior that objectFound meant the "name" field.
    # //note that: the isA condition from objectFound->object to object,
    # //IE from name->name->type to name->type,
    # //has to be checked BEFORE!.
    # //-- huh, DERP
end

struct SyntaxInstChoice <: SyntaxInst
    name::SyntaxChoice
    flag::Int
    choice::SyntaxInst
    PofThisAndBelowGivenBelow::Real #//that is, the CONJUGATE, that works as a posterior, UP TO HERE
end

mutable struct SyntaxInstStruct <: SyntaxInstProduct
    name::SyntaxStruct
    list::Array{SyntaxInst}
    PofThisAndBelowGivenBelow::Real #  //that is, the CONJUGATE, that works as a posterior, UP TO HERE
    # //std::optional<ATermBuilder> meetedReferences =std::nullopt;
end

mutable struct SyntaxInstStrip <: SyntaxInstProduct
    name::SyntaxStrip
    list::Array{SyntaxInst}  #//So... SHOULDNT THESE BE OF A >cONSTANT< >tYPE< SOMEHOW??? <<<
    PofThisAndBelowGivenBelow::Real #//that is, the CONJUGATE, that works as a posterior, UP TO HERE
    # //std::optional<ATermBuilder Owning>meetedReferences;
end


getP(s::SyntaxInstTerm)::Real = s.P
getP(s::SyntaxInstReference)::Real = s.P
getP(s::SyntaxInstNativeString)::Real = s.P
getP(s::SyntaxInstObject)::Real = s.PofObjectAndBelowGivenBelow
getP(s::SyntaxInstField)::Real = s.PofThisAndBelowGivenBelow
getP(s::SyntaxInstChoice)::Real = s.PofThisAndBelowGivenBelow
getP(s::SyntaxInstStruct)::Real = s.PofThisAndBelowGivenBelow
getP(s::SyntaxInstStrip)::Real = s.PofThisAndBelowGivenBelow

trace(s::SyntaxInstTerm)::String = getString(s.name)
trace(s::SyntaxInstReference)::String = s.text
trace(s::SyntaxInstNativeString)::String = s.text
trace(s::SyntaxInstObject)::String = "FOUND{"*trace(s.syntax)*"}"
trace(s::SyntaxInstField)::String = trace(s.objectFound)
trace(s::SyntaxInstChoice)::String = "[<$(string(s.flag))>: $(s.choice |> trace)]"
trace(s::SyntaxInstStruct)::String = join(s.list .|> trace, " ")
trace(s::SyntaxInstStrip)::String = "(" * join(s.list .|> trace, " ") * ")"

deepEqual(s::SyntaxInstTerm, other::SyntaxInst)::Bool = other isa SyntaxInstTerm && s.name == other.name
deepEqual(s::SyntaxInstReference, other::SyntaxInst)::Bool = other isa SyntaxInstReference && s.type == other.type && s.name == other.name
deepEqual(s::SyntaxInstNativeString, other::SyntaxInst)::Bool = other isa SyntaxInstNativeString && s.text == other.text
deepEqual(s::SyntaxInstObject, other::SyntaxInst)::Bool = other isa SyntaxInstObject && other.name == name && deepEqual(s.syntax, other.syntax)
deepEqual(s::SyntaxInstField, other::SyntaxInst)::Bool = other isa SyntaxInstField && s.name == other.name
# // LOL THIS WILL BE WRONG IN THE FUTURE ^
# //LOL GOOD LUCK WITH FINDING THIS BUG, ALSO
deepEqual(s::SyntaxInstChoice, other::SyntaxInst)::Bool = other isa SyntaxInstChoice && other.name == s.name && other.flag == s.flag && other.choice == s.choice
deepEqual(s::SyntaxInstStruct, other::SyntaxInst)::Bool = other isa SyntaxInstStruct && s.name == other.name && all([deepEqual(i1, i2) for (i1, i2) in zip(s.list, other.list)])
deepEqual(s::SyntaxInstStrip, other::SyntaxInst)::Bool = other isa SyntaxInstStrip && s.name == other.name && all([deepEqual(i1, i2) for (i1, i2) in zip(s.list, other.list)])



function push_struct!(s::SyntaxInstStruct, obj::SyntaxInst, index::Int, marginalOfObjName::Real)
    if !(index == length(s.list) && wouldFit(obj, s.name.list[index+1])) throw(DomainError("freganiente")) end
    # ^ //this part is for testing: cuz, u are SUPPOSED TO KNOW WAT YOU'RE DOING
    # //also, now this is DOUBLE BAD because would_fit CAN get expensive (so maybe not call it at random?)
    push!(s.list, obj)
    # //UPDATE PROB HERE, PLEASE: >>HOPEFULLY THIS IS NOT COMPLETELY WRONG::<<
    s.PofThisAndBelowGivenBelow *= (getP(obj) / marginalOfObjName);
end
function insert_front!(s::SyntaxInstStruct, obj::SyntaxInst, index::Int, marginalOfObjName::Real)
    if !(index == length(s.name.list) - length(s.list) - 1 && wouldFit(obj, s.name.list[index+1])) throw(DomainError("freganiente")) end
    # ^ //this part is for testing: cuz, u are SUPPOSED TO KNOW WAT YOU'RE DOING
    # //also, now this is DOUBLE BAD because would_fit CAN get expensive (so maybe not call it at random?)
    s.list = vcat([obj], s.list)
    # //UPDATE PROB HERE, PLEASE: >>HOPEFULLY THIS IS NOT COMPLETELY WRONG::<<
    s.PofThisAndBelowGivenBelow *= (getP(obj) / marginalOfObjName);
end


function push_struct!(s::SyntaxInstStrip, obj::SyntaxInst, index::Int, marginalOfObjName::Real)
    # //I HONESTLY CANT BE BOTHERED
    push!(s.list, obj);
    # //SEE SyntaxInstStruct FOR HOW THIS SHOULD BE WORKING
    # //and, also: update prob here, please:  >>>again, HOPEFULLY THIS IS NOT COMPLETELY WRONG::<<
    s.PofThisAndBelowGivenBelow *= (getP(obj) / marginalOfObjName);
end
function insert_front!(s::SyntaxInstStrip, obj::SyntaxInst, index::Int, marginalOfObjName::Real)
    # //idem^
    s.list = vcat([obj], s.list)
    # //idem^^
    s.PofThisAndBelowGivenBelow *= (getP(obj) / marginalOfObjName);
end
