
include("Syntaxes.jl")
# it REQUIRES that you included ("mylambda1.jl") at Some Point!!!

abstract type SyntaxInst end
abstract type Accepted_SynatxInst_type <: SyntaxInst end
# ^ SyntaxInstObject, SyntaxInstReference, SyntaxInstSimpleString <: Accepted_SynatxInst_type;
abstract type SyntaxInstProduct <: SyntaxInst end

wouldFit(si::SyntaxInst, s::SyntaxCore)::Bool = si.name == s
getName(s::SyntaxInst) = s.name

struct SyntaxInstTerm <: SyntaxInst
    name::SyntaxTerm
	P::Real  # //I might be wrong, but this is just the marginal
end

struct SyntaxInstReference <: Accepted_SynatxInst_type
    # //it's a variable.
    # //note: the name of a Term is the USE OF A GLOBALLY DEFINED VARIABLE # (Will i have to fix this?)
    # //note: a variable definition CONTAINS A VARIABLE (i.e., the name.)
	type::Term # //it contains THE TYPE OF THE VAR YOU ARE JUST REFERENCING
	text::String #
	P::Real # //What is this, really? I contains the likelyhood of type being represented by a free variable, and the similarity of the sentence maybe?
    # inferred_term will have the very simple form TAnno(TLocStr(text), type)
end

struct SyntaxInstSimpleString <: Accepted_SynatxInst_type
    # //it's a string
	name::SyntaxSimpleString
	text::String
	P::Real # //What is this, really? Prob a constant? Or >>1<<?
    # ^ This has the very simple form TAnno(TStr(text), TS())
end

struct SyntaxInstObject <: Accepted_SynatxInst_type
    # //a syntax that results in a obj
    # name::Term # This is THE TYPE OF THE OBJ YOU JUST FOUND
    syntax::SyntaxInst  # //it is THE SYNTAX THAT OBJECT IS USING
    PofObjectAndBelowGivenBelow::Real #//it's the P of the fact that syntax meant object, times P of syntax and stuff.
    inferred_obj::TAnno # This HAS BEEN BUIT UP ALREADY. BUT, it still has Holes ot Type variables ofc!! Also: it CAN be an Errored one!!
end

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

function getObjects(s::SyntaxInstStrip)
    if s.name.before === nothing
        Array{SyntaxInst}([s.list[i*2-1] for i in 1:((length(s.list)+1)÷2)])
    else
        Array{SyntaxInst}([s.list[i*2] for i in 1:((length(s.list)-1)÷2)])
    end
end

getP(s::SyntaxInstTerm)::Real = s.P
getP(s::SyntaxInstReference)::Real = s.P
getP(s::SyntaxInstSimpleString)::Real = s.P
getP(s::SyntaxInstObject)::Real = s.PofObjectAndBelowGivenBelow
getP(s::SyntaxInstField)::Real = s.PofThisAndBelowGivenBelow
getP(s::SyntaxInstChoice)::Real = s.PofThisAndBelowGivenBelow
getP(s::SyntaxInstStruct)::Real = s.PofThisAndBelowGivenBelow
getP(s::SyntaxInstStrip)::Real = s.PofThisAndBelowGivenBelow

trace(s::SyntaxInstTerm; top=false)::String = getString(s.name)
trace(s::SyntaxInstReference; top=false)::String = s.text
trace(s::SyntaxInstSimpleString; top=false)::String = s.text
trace(s::SyntaxInstObject; top=false)::String = (
    "FOUND{$(trace(s.syntax))" *
    (top ? (" (inferred to a $(s.inferred_obj.expr|>typeof) obj, $(s.inferred_obj.expr|>pr_E) of type $(s.inferred_obj.type|>pr))})}") : "}"))
trace(s::SyntaxInstField; top=false)::String = trace(s.objectFound)
trace(s::SyntaxInstChoice; top=false)::String = "[<$(string(s.flag))>: $(s.choice |> trace)]"
trace(s::SyntaxInstStruct; top=false)::String = join(s.list .|> trace, " ")
trace(s::SyntaxInstStrip; top=false)::String = "(" * join(s.list .|> trace, " ") * ")"

deepEqual(s::SyntaxInstTerm, other::SyntaxInst)::Bool = other isa SyntaxInstTerm && s.name == other.name
deepEqual(s::SyntaxInstReference, other::SyntaxInst)::Bool = other isa SyntaxInstReference && s.type === other.type && s.name == other.name
deepEqual(s::SyntaxInstSimpleString, other::SyntaxInst)::Bool = other isa SyntaxInstSimpleString && s.text == other.text
deepEqual(s::SyntaxInstObject, other::SyntaxInst)::Bool = other isa SyntaxInstObject && other.inferred_obj === getInferredTerm(s) && deepEqual(s.syntax, other.syntax)
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






struct SyntWithItsBuilderFunc
	syntax::SyntaxCore
	builder_func::Any
    # Any is a (Dict{String, Union{Term,Error}}) -> Union{TAnno, Error}  lambda !!!
    # OR a (Array{Union{Term,Error}}) -> Union{TAnno, Error}  lambda !!!
	P::Real
end

# HELPER: collect_fields looks for SyntaxInstField's and extract a name=>obj dict.
# It looks at the whole tree, and it only doesnt know how to handle SyntaxInstStrip's.
collect_fields(s::SyntaxInstTerm)::Dict{String, TAnno} = Dict{String, TAnno}()
collect_fields(s::SyntaxInstReference)::Dict{String, TAnno} = Dict{String, TAnno}()
collect_fields(s::SyntaxInstSimpleString)::Dict{String, TAnno} = Dict{String, TAnno}()
collect_fields(s::SyntaxInstObject)::Dict{String, TAnno} = Dict{String, TAnno}()
collect_fields(s::SyntaxInstField)::Dict{String, TAnno} = Dict{String, TAnno}(s.name.name=>getObjFoundFromAccepted(s.objectFound; as_type=s.name.type))
collect_fields(s::SyntaxInstChoice)::Dict{String, TAnno} = collect_fields(s.choice)
collect_fields(s::SyntaxInstStruct)::Dict{String, TAnno} = merge((s.list .|> (x->collect_fields(x)))...)
function collect_fields(s::SyntaxInstStrip)::Dict{String, TAnno}
    throw(DomainError("When is a field ever represented by a SyntaxStrip ???"))
end
collect_simpleStrings(s::SyntaxInstTerm)::Dict{String, String} = Dict{String, String}()
collect_simpleStrings(s::SyntaxInstReference)::Dict{String, String} = Dict{String, String}()
collect_simpleStrings(s::SyntaxInstSimpleString)::Dict{String, String} = Dict{String, String}(s.name.name=>s.text)
collect_simpleStrings(s::SyntaxInstObject)::Dict{String, String} = Dict{String, String}()
collect_simpleStrings(s::SyntaxInstField)::Dict{String, String} = Dict{String, String}()
collect_simpleStrings(s::SyntaxInstChoice)::Dict{String, String} = collect_simpleStrings(s.choice)
collect_simpleStrings(s::SyntaxInstStruct)::Dict{String, String} = merge((s.list .|> (x->collect_simpleStrings(x)))...)
function collect_fields(s::SyntaxInstStrip)::Dict{String, String}
    println("To be clear: A field can ABSOLUTELY be represented by a SyntaxStrip, just, I wont look into it...")
    Dict{String, String}()
end

# HELPER: collect_objs works on Accepted_SynatxInst_type's and returns it.
# If it founds a SyntaxInstField, it looks into its .objectFound. Otherwise, it's an error.
collect_objs(s::SyntaxInstTerm) = nothing
collect_objs(s::SyntaxInstReference) = s
collect_objs(s::SyntaxInstSimpleString) = s
collect_objs(s::SyntaxInstObject) = s
collect_objs(s::SyntaxInstField) = collect_objs(s.objectFound)
collect_objs(s::SyntaxInstChoice) = nothing
collect_objs(s::SyntaxInstStruct) = nothing
collect_objs(s::SyntaxInstStrip) = nothing

function collect_strip_tannos(s::SyntaxInstStrip)::Array{TAnno}
    objs = s |>getObjects .|> collect_objs
    @assert all([ss !== nothing for ss in objs]) "Which SyntaxInstStrip has Syntax that are not Accepted_SynatxInst_type ..... (Him: $(s|>trace), with types $(s.list .|>typeof))"
    gof = (x->getObjFoundFromAccepted(x))
    # MISSING: as_type               ^
    objs .|> gof
end

function getObjFoundFromAccepted(s::Accepted_SynatxInst_type; as_type::Union{Nothing, Term} = nothing)::TAnno
    if s isa SyntaxInstReference && as_type !== nothing
        @assert s.type == as_type "This is only diagnostic. Ofc it is. If not, tough luck LOL"
    end
    return getInferredTerm(s) # TODO:  |> transform_in<as_type>
end

getInferredTerm(s::SyntaxInstReference)::TAnno = TAnno(TLocStr(s.text), TTerm(TProd(Dict{Id,Term}(s.text => s.type)), s.type))
getInferredType(s::SyntaxInstReference)::Term = TTermAuto(s.type, s.type)

getInferredTerm(s::SyntaxInstSimpleString)::TAnno = TAnno(TStr(s.text), TS())
getInferredType(s::SyntaxInstSimpleString)::Term = TTermEmpty(TS()) # OR TS()
# OR, strinType=TypeSumTerm("String", 2, TTop()) for the type, MAYBE???

getInferredTerm(s::SyntaxInstObject)::TAnno = s.inferred_obj
getInferredType(s::SyntaxInstObject)::Term = s.inferred_obj.type


