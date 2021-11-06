
include("RandomParser10.jl")

SMap = Dict{String, SyntaxCore}
TMap = Dict{String, Temp_Type}



SyntaxTerms = Dict{String, SyntaxTerm}()
SyntaxFields = Dict{String, SyntaxField}()
SyntaxChoicess = Dict{String, SyntaxChoice}()
SyntaxStructs = Dict{String, SyntaxStruct}()
SyntaxStrips = Dict{String, SyntaxStrip}()

TypeBases = Dict{String, Temp_TypeBase}()
TypeFuncs = Dict{String, Temp_TypeFunc}()
TypeSums = Dict{String, Temp_TypeSum}()
TypeProds = Dict{String, Temp_TypeProd}()

Dict{Temp_Type, SyntaxCore} bindings()

# //base words
for i in ["{", "-",">",":","=","(",")",";","where","Type","eval","}"]
	SyntaxTerms[i] =SyntaxTerm(i)
end


function makeNiceTreeStructure(leafName::String, productBranchName::String, sumName::String, fieldNameFirst::String, FieldNameSecond::String)
	# //creates a nice tree that is made like this: T = A + (T x T) where A is a Temp_TypeBase with a name

	TypeBases[leafName] = Temp_TypeBase(leafName)
	TypeProds[productBranchName] = Temp_TypeProd()
	TypeSums[sumName] = Temp_TypeSum([TypeProds[productBranchName], TypeBases[leafName] ])

	######################### NOTE: This prod has STR NAMES associated w/ fields, ALREADY!!!
	TypeProds[productBranchName].data[fieldNameFirst]= TypeSums[sumName]
	SyntaxFields[fieldNameFirst] = SyntaxField(fieldNameFirst, TypeSums[sumName])

	TypeProds[productBranchName].data[FieldNameSecond] = TypeSums[sumName]
	SyntaxFields[FieldNameSecond] = SyntaxField(FieldNameSecond, TypeSums[sumName])
end

function addFieldToProductWithSintaxfield(whichProduct::String, fieldName::String, whichField::Temp_Type)
	######################### NOTE: This prod has STR NAMES associated w/ fields, ALREADY!!!
	TypeProds[whichProduct].data[fieldName] = whichField
	SyntaxFields[fieldName] = SyntaxField(fieldName, whichField)
end

text = "ff:(A->B)-> B  where ff (  g  )  =  g  (  a ) ; eval ff ( h ) ";


# // type expession: T = A + ("T -> T") where A is base type and "T -> T" is the function type
makeNiceTreeStructure("baseTypeVariable", "functionType", "type", "first", "second");

SyntaxStructs["functionType_S_noPar"] = SyntaxStruct(Array{SyntaxCore}([SyntaxFields["first"], SyntaxTerms["-"], SyntaxTerms[">"], SyntaxFields["second"]]))
SyntaxStructs["functionType_S_Par"] = SyntaxStruct(Array{SyntaxCore}([SyntaxTerms["("], SyntaxStructs["functionType_S_noPar"], SyntaxTerms[")"]]))
SyntaxChoicess["functionType_S"] = SyntaxChoice(Array{SyntaxCore}([SyntaxStructs["functionType_S_Par"], SyntaxStructs["functionType_S_noPar"]]))

bindings[TypeProds["functionType"]] = SyntaxChoicess["functionType_S"] # //it HAS BEEN:  << SyntaxChoicess.getSyntaxCore("functionType_S_Par_noPar");



# //terms expression: t = a + "t(t)" where a is a variable and t(t) is a function application
makeNiceTreeStructure("variable", "funcApp", "term", "func", "arg")#//FINALLY, FUOND WHERE IT BREAKS
																	#	//this DOES NOT SURPRISE US
																	#	//this, WAS ABOUT TIME

SyntaxStructs["funcApp_S"] = SyntaxStruct(Array{SyntaxCore}([SyntaxFields["func"], SyntaxTerms["("], SyntaxFields["arg"], SyntaxTerms[")"]]))
bindings[TypeProds["funcApp"]] = SyntaxStructs["funcApp_S"]

# //// ok

# //base type def: syntax "A: Type" where A is the name of the type
TypeProds["baseTypeDef"] = Temp_TypeProd([])

# ///ALSO I'M _REALLY_ NOT SURE ABOUT THE NEXT LINES.........................
addFieldToProductWithSintaxfield("baseTypeDef", "BaseTypeDef_name", TypeBases["baseTypeVariable"])

SyntaxStructs["BaseTypeDef_S"] = SyntaxStruct(Array{SyntaxCore}([SyntaxFields["BaseTypeDef_name"], SyntaxTerms[":"], SyntaxTerms["Type"]]))
bindings[TypeProds["baseTypeDef"]] = SyntaxStructs["BaseTypeDef_S"]


# //term def: syntax "a: T" where a is the name of the variable and T is a type
TypeProds["variableTermDef"] = Temp_TypeProd([])

addFieldToProductWithSintaxfield("variableTermDef", "variableTermDef_name", TypeBases["variable"])
addFieldToProductWithSintaxfield("variableTermDef", "variableTermDef_type", TypeSums["type"])

SyntaxStructs["variableTermDef_S"] = SyntaxStruct(Array{SyntaxCore}([SyntaxFields["variableTermDef_name"], SyntaxTerms[":"], SyntaxFields["variableTermDef_type"]]))
bindings[TypeProds["variableTermDef"]] = SyntaxStructs["variableTermDef_S"]


# //funcion definition and declaration:
# //syntax "f: T where f(x)={t}" where f is the function name, T is a type, and t is a term.
TypeProds["funcDefAndDecl"] = Temp_TypeProd([])

addFieldToProductWithSintaxfield("funcDefAndDecl", "funcDefAndDecl_name", TypeBases["variable"])
addFieldToProductWithSintaxfield("funcDefAndDecl", "funcDefAndDecl_type", TypeSums["type"])
addFieldToProductWithSintaxfield("funcDefAndDecl", "funcDefAndDecl_parameter", TypeProds["variableTermDef"])
addFieldToProductWithSintaxfield("funcDefAndDecl", "funcDefAndDecl_body", TypeSums["term"])

SyntaxStructs["funcDefAndDecl_S"] = SyntaxStruct(Array{SyntaxCore}([SyntaxFields["funcDefAndDecl_name"], SyntaxTerms[":"], SyntaxFields["funcDefAndDecl_type"], SyntaxTerms["where"], SyntaxFields["funcDefAndDecl_name"], SyntaxTerms["("], SyntaxFields["funcDefAndDecl_parameter"], SyntaxTerms[")"], SyntaxTerms["="], SyntaxFields["funcDefAndDecl_body"]]))
bindings[TypeProds["funcDefAndDecl"]] = SyntaxStructs["funcDefAndDecl_S"]


# //eval sentence
TypeProds["evalSentence"] = Temp_TypeProd([])

addFieldToProductWithSintaxfield("evalSentence", "evalSentence_term", TypeSums["term"])

SyntaxStructs["evalSentence_S"] = SyntaxStruct(Array{SyntaxCore}([ SyntaxTerms["eval"], SyntaxFields["evalSentence_term"]]))
bindings[TypeProds["evalSentence"]] = SyntaxStructs["evalSentence_S"]


# //DUMB program, just for show: a program is a funcDefAndDecl, then ";", then an eval:
TypeProds["program"]=Temp_TypeProd([])

addFieldToProductWithSintaxfield("program", "program_funcdef", TypeProds["funcDefAndDecl"])
addFieldToProductWithSintaxfield("program", "program_eval", TypeProds["evalSentence"])

SyntaxStructs["program_S"] = SyntaxStruct(Array{SyntaxCore}([SyntaxFields["program_funcdef"], SyntaxTerms[";"], SyntaxFields["program_eval"]]))
bindings[TypeProds["program"]] = SyntaxStructs["program_S"]

randomParser10 = RandomParser10()

for (name, s) in SyntaxTerms  addSyntax(randomParser10.structure.posteriorsStructure, name, s) end
for (name, s) in SyntaxFields  addSyntax(randomParser10.structure.posteriorsStructure, name, s) end
for (name, s) in SyntaxChoicess  addSyntax(randomParser10.structure.posteriorsStructure, name, s) end
for (name, s) in SyntaxStructs  addSyntax(randomParser10.structure.posteriorsStructure, name, s) end
for (name, s) in SyntaxStrips  addSyntax(randomParser10.structure.posteriorsStructure, name, s) end

for (s, t) in bindings push!(randomParser10.structure.posteriorsStructure.bindings[t], s) end

initializeMarginals(randomParser10.structure.posteriorsStructure)
initializeChoices(randomParser10.structure.posteriorsStructure)
initializeStrips(randomParser10.structure.posteriorsStructure)
initializePosteriors(randomParser10.structure.posteriorsStructure)


parse(randomParser10, text)


res = getBestTotalFound(randomParser10)
if res!==nothing && res isa SyntaxInstStruct
	program_S_point = getSyntax(randomParser10.structure.posteriorsStructure, "program_S")
	println(res->getSynt(), " ", program_S_point, "\n")
	println("K fine\n")
end



# //randomParser10.getBestTotalFound.? get.{as SyntaxInstStruct->x | as _->None}.? name.display, WHICH IS OF TYPE: Action + 1, WHATEVER THIS MEANS






# int main3()

# // this is the text you MEAN to use (you just compile it, not parse it):
text::String = "a:A; (1.a):A+B"

# // type expession: T = A + ("T -> T") where A is base type and "T -> T" is the function type
makeNiceTreeStructure("baseTypeVariable", "SumType", "type", "case1", "case2")




