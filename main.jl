
include("Parser/RandomParser10.jl")

s = SyntaxTerm("+")
si = SyntaxInstTerm(s, 1)
s = SyntaxChoice([s, s])
si = SyntaxInstChoice(s, 0, si, 1)
s = SyntaxStruct([s,s])
si = SyntaxInstStruct(s, [si, si], 1)
s = SyntaxField("a", Temp_TypeBase("A"))
si = SyntaxInstReference(Temp_TypeBase("A"), "UHH", 1)
si = SyntaxInstNativeString("iii", 1)
si = SyntaxInstObject(Temp_TypeBase("A"), si, 1)
si = SyntaxInstField(s, si, 1)
# s = SyntaxStrip()
# si = SyntaxInstStrip()

fs = FinishedsStructure10(3); fs|>trace
getS(s) = SyntaxInstOwner(SyntaxInstTerm(SyntaxTerm(s), 1))

fs = FinishedsStructure10([getS("+"), getS("-"), getS(":")]); fs|>trace
reshape(fs, 0, 1, 1); fs|>trace
reshape(fs, 0, 0, 1); fs|>trace
reshape(fs, 0, 1, 0); fs|>trace
reshape(fs, 0, 2, 3); fs|>trace
reshape(fs, 0, 2, 2); fs|>trace

reshape(fs, 3, 3, 1); fs|>trace
reshape(fs, 2, 3, 3); fs|>trace
reshape(fs, 2, 3, 0); fs|>trace
reshape(fs, 3, 3, 2); fs|>trace

fs = FinishedsStructure10([getS("+"), getS("-"), getS(":")]); fs|>trace
set(fs, 0,2,[getS("+-")]); fs|>trace
@assert [s for s in IterableForElementsEndingAt(fs.matrix, 1)] |> length == 1
@assert [s for s in IterableForElementsEndingAt(fs.matrix, 2)] |> length == 2
@assert [s for s in IterableForElementsEndingAt(fs.matrix, 3)] |> length == 1
@assert [s for s in IterableForElementsStartingFrom(fs.matrix, 0)] |> length == 2
@assert [s for s in IterableForElementsStartingFrom(fs.matrix, 1)] |> length == 1
@assert [s for s in IterableForElementsStartingFrom(fs.matrix, 2)] |> length == 1


# OK!^

get_hc_beg(s::String) = HangingChance10(
    SyntaxStruct([SyntaxTerm(s),SyntaxTerm("=")]),
    SyntaxInstTerm(SyntaxTerm(s), 1),
    0, 1,
    1, 1)
get_hc_beg("+")
get_hc_end(s::String) = HangingChance10(
    SyntaxStruct([SyntaxTerm("+"),SyntaxTerm(s)]),
    SyntaxInstTerm(SyntaxTerm(s), 1),
    1, 1,
    1, 1)
get_hc_end("+")

function get_cs()
    cs = ChancesStructure10()
    reshape(cs, 0,0,3)
    addBeginning(cs, get_hc_beg("+"), 1)
    addBeginning(cs, get_hc_beg("+"), 1)
    addEnding(cs, get_hc_end("="), 1)
    addEnding(cs, get_hc_end("="), 2)
    println(cs.beginnings.|>length), println(cs.endings.|>length);
    cs
end

cs = get_cs();

# reshape(cs, 0,1,0); println(cs.beginnings.|>length), println(cs.endings.|>length);# YES
# reshape(cs, 0,0,1); println(cs.beginnings.|>length), println(cs.endings.|>length);# deleting too much
# reshape(cs, 0,1,1); println(cs.beginnings.|>length), println(cs.endings.|>length);# YES

# reshape(cs, 2,3,0); println(cs.beginnings.|>length), println(cs.endings.|>length);# YES
# reshape(cs, 2,3,2); println(cs.beginnings.|>length), println(cs.endings.|>length);# YES
# reshape(cs, 3,3,2); println(cs.beginnings.|>length), println(cs.endings.|>length);# YES



########## Parsing 1: Parse "+"

# s10 = Structure10()
# addSyntax!(s10.posteriorsStructure, "+", SyntaxTerm("+"))
# initializeMarginals(s10.posteriorsStructure)
# initializeChoices(s10.posteriorsStructure)
# initializePosteriors(s10.posteriorsStructure)
# # initializeStrips(s10.posteriorsStructure)

# # insertTerminal(s10, 0,1,SyntaxTerm("+"), 1)
# # s10.finisheds|>trace
# # doTheBestYouCan(s10)
# # s10.finisheds|>trace


# rp = RandomParser10("", [], s10)
# parse(rp, "+")
# rp.structure|>trace



########## Parsing 2: Parse "->"

s10 = Structure10()

SyntaxTerms = Dict{String, SyntaxTerm}()
SyntaxFields = Dict{String, SyntaxField}()
SyntaxChoicess = Dict{String, SyntaxChoice}()
SyntaxStructs = Dict{String, SyntaxStruct}()
SyntaxStrips = Dict{String, SyntaxStrip}()
TypeBases = Dict{String, Temp_TypeBase}()
TypeFuncs = Dict{String, Temp_TypeFunc}()
TypeSums = Dict{String, Temp_TypeSum}()
TypeProds = Dict{String, Temp_TypeProd}()
bindings = Dict{Temp_Type, SyntaxCore}()

for i in ["{", "-",">"] SyntaxTerms[i] =SyntaxTerm(i) end
SyntaxStructs["arrow"] = SyntaxStruct(Array{SyntaxCore}([SyntaxTerms["-"], SyntaxTerms[">"]]))
SyntaxChoicess["arrow_S"] = SyntaxChoice(Array{SyntaxCore}([SyntaxStructs["arrow"]]))

for (name, s) in SyntaxTerms  addSyntax!(s10.posteriorsStructure, name, s) end
for (name, s) in SyntaxChoicess  addSyntax!(s10.posteriorsStructure, name, s) end
for (name, s) in SyntaxStructs  addSyntax!(s10.posteriorsStructure, name, s) end
initializeMarginals(s10.posteriorsStructure)
initializeChoices(s10.posteriorsStructure)
initializePosteriors(s10.posteriorsStructure)


# text = "->"

# rp = RandomParser10("", [], s10);
# parse(rp, text)  # OOf
# rp.structure|>trace
# rp.structure.hangings.beginnings







########## Parsing 3: Parse "T->T"

function make_s10()
    s10 = Structure10()

    SyntaxTerms = Dict{String, SyntaxTerm}()
    SyntaxFields = Dict{String, SyntaxField}()
    SyntaxChoicess = Dict{String, SyntaxChoice}()
    SyntaxStructs = Dict{String, SyntaxStruct}()
    SyntaxStrips = Dict{String, SyntaxStrip}()
    TypeBases = Dict{String, Temp_TypeBase}()
    TypeFuncs = Dict{String, Temp_TypeFunc}()
    TypeSums = Dict{String, Temp_TypeSum}()
    TypeProds = Dict{String, Temp_TypeProd}()
    bindings = Dict{Temp_Type, SyntaxCore}()

    # // type expession: T = A + ("T -> T") where A is base type and "T -> T" is the function type
    # makeNiceTreeStructure("baseTypeVariable", "functionType", "type", "first", "second");

    leafName = "baseTypeVariable"
    productBranchName = "functionType"
    fieldNameFirst = "first"
    FieldNameSecond = "second"
    TypeBases[leafName] = Temp_TypeBase(leafName)
    TypeProds[productBranchName] = Temp_TypeProd(Array{Temp_Type}([]))

    TypeProds[productBranchName].objs[fieldNameFirst]= TypeBases[leafName]
    SyntaxFields[fieldNameFirst] = SyntaxField(fieldNameFirst, TypeBases[leafName])
    TypeProds[productBranchName].objs[FieldNameSecond] = TypeBases[leafName]
    SyntaxFields[FieldNameSecond] = SyntaxField(FieldNameSecond, TypeBases[leafName])

    for i in ["{", "-",">",":","=","(",")",";","where","Type","eval","}"] SyntaxTerms[i] =SyntaxTerm(i) end
    SyntaxStructs["functionType_S_noPar"] = SyntaxStruct(Array{SyntaxCore}([SyntaxFields["first"], SyntaxTerms["-"], SyntaxTerms[">"], SyntaxFields["second"]]))
    SyntaxStructs["functionType_S_Par"] = SyntaxStruct(Array{SyntaxCore}([SyntaxTerms["("], SyntaxStructs["functionType_S_noPar"], SyntaxTerms[")"]]))
    SyntaxChoicess["functionType_S"] = SyntaxChoice(Array{SyntaxCore}([SyntaxStructs["functionType_S_Par"], SyntaxStructs["functionType_S_noPar"]]))
    bindings[TypeProds["functionType"]] = SyntaxChoicess["functionType_S"] # //it HAS BEEN:  << SyntaxChoicess.getSyntaxCore("functionType_S_Par_noPar");

    TypeProds["baseTypeDef"] = Temp_TypeProd(Array{Temp_Type}([]))
    whichProduct = "baseTypeDef"; fieldName = "BaseTypeDef_name"; whichField = TypeBases["baseTypeVariable"]
    TypeProds[whichProduct].objs[fieldName] = whichField
    SyntaxFields[fieldName] = SyntaxField(fieldName, whichField)
    SyntaxStructs["BaseTypeDef_S"] = SyntaxStruct(Array{SyntaxCore}([SyntaxFields["BaseTypeDef_name"], SyntaxTerms[":"], SyntaxTerms["Type"]]))
    bindings[TypeProds["baseTypeDef"]] = SyntaxStructs["BaseTypeDef_S"]

    for (name, s) in SyntaxTerms  addSyntax!(s10.posteriorsStructure, name, s) end
    for (name, s) in SyntaxFields  addSyntax!(s10.posteriorsStructure, name, s) end
    for (name, s) in SyntaxChoicess  addSyntax!(s10.posteriorsStructure, name, s) end
    for (name, s) in SyntaxStructs  addSyntax!(s10.posteriorsStructure, name, s) end
    for (name, s) in SyntaxStrips  addSyntax!(s10.posteriorsStructure, name, s) end
    initializeMarginals(s10.posteriorsStructure)
    initializeChoices(s10.posteriorsStructure)
    initializePosteriors(s10.posteriorsStructure)

    for (s, t) in bindings
        if !(t in keys(s10.posteriorsStructure.bindings))
            s10.posteriorsStructure.bindings[t] = [s]
        else
            push!(s10.posteriorsStructure.bindings[t], s)
        end
    end
    return s10
end

# text = "A->B"
# s10 = make_s10();
# rp = RandomParser10("", [], s10);
# parse(rp, text)
# rp.structure |> trace
# rp.structure.finisheds.matrix[1][end][end].s.list #|> trace







########## Parsing 4: Parse The original example!!

function make_s10_big()

    SyntaxTerms = Dict{String, SyntaxTerm}()
    SyntaxFields = Dict{String, SyntaxField}()
    SyntaxChoicess = Dict{String, SyntaxChoice}()
    SyntaxStructs = Dict{String, SyntaxStruct}()
    SyntaxStrips = Dict{String, SyntaxStrip}()

    TypeBases = Dict{String, Temp_TypeBase}()
    TypeFuncs = Dict{String, Temp_TypeFunc}()
    TypeSums = Dict{String, Temp_TypeSum}()
    TypeProds = Dict{String, Temp_TypeProd}()

    bindings = Dict{Temp_Type, SyntaxCore}()

    # //base words
    for i in ["{", "-",">",":","=","(",")",";","where","Type","eval","}"]
        SyntaxTerms[i] =SyntaxTerm(i)
    end


    function makeNiceTreeStructure(leafName::String, productBranchName::String, sumName::String, fieldNameFirst::String, FieldNameSecond::String)
        # //creates a nice tree that is made like this: T = A + (T x T) where A is a Temp_TypeBase with a name

        TypeBases[leafName] = Temp_TypeBase(leafName)
        TypeProds[productBranchName] = Temp_TypeProd(Array{Temp_Type}([]))
        TypeSums[sumName] = Temp_TypeSum([TypeProds[productBranchName], TypeBases[leafName] ])

        ######################### NOTE: This prod has STR NAMES associated w/ fields, ALREADY!!!
        TypeProds[productBranchName].objs[fieldNameFirst]= TypeSums[sumName]
        SyntaxFields[fieldNameFirst] = SyntaxField(fieldNameFirst, TypeSums[sumName])

        TypeProds[productBranchName].objs[FieldNameSecond] = TypeSums[sumName]
        SyntaxFields[FieldNameSecond] = SyntaxField(FieldNameSecond, TypeSums[sumName])
    end

    function addFieldToProductWithSintaxfield(whichProduct::String, fieldName::String, whichField::Temp_Type)
        ######################### NOTE: This prod has STR NAMES associated w/ fields, ALREADY!!!
        TypeProds[whichProduct].objs[fieldName] = whichField
        SyntaxFields[fieldName] = SyntaxField(fieldName, whichField)
    end



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
    TypeProds["baseTypeDef"] = Temp_TypeProd(Array{Temp_Type}([]))

    # ///ALSO I'M _REALLY_ NOT SURE ABOUT THE NEXT LINES.........................
    addFieldToProductWithSintaxfield("baseTypeDef", "BaseTypeDef_name", TypeBases["baseTypeVariable"])

    SyntaxStructs["BaseTypeDef_S"] = SyntaxStruct(Array{SyntaxCore}([SyntaxFields["BaseTypeDef_name"], SyntaxTerms[":"], SyntaxTerms["Type"]]))
    bindings[TypeProds["baseTypeDef"]] = SyntaxStructs["BaseTypeDef_S"]


    # //term def: syntax "a: T" where a is the name of the variable and T is a type
    TypeProds["variableTermDef"] = Temp_TypeProd(Array{Temp_Type}([]))

    addFieldToProductWithSintaxfield("variableTermDef", "variableTermDef_name", TypeBases["variable"])
    addFieldToProductWithSintaxfield("variableTermDef", "variableTermDef_type", TypeSums["type"])

    SyntaxStructs["variableTermDef_S"] = SyntaxStruct(Array{SyntaxCore}([SyntaxFields["variableTermDef_name"], SyntaxTerms[":"], SyntaxFields["variableTermDef_type"]]))
    bindings[TypeProds["variableTermDef"]] = SyntaxStructs["variableTermDef_S"]


    # //funcion definition and declaration:
    # //syntax "f: T where f(x)={t}" where f is the function name, T is a type, and t is a term.
    TypeProds["funcDefAndDecl"] = Temp_TypeProd(Array{Temp_Type}([]))

    addFieldToProductWithSintaxfield("funcDefAndDecl", "funcDefAndDecl_name", TypeBases["variable"])
    addFieldToProductWithSintaxfield("funcDefAndDecl", "funcDefAndDecl_type", TypeSums["type"])
    addFieldToProductWithSintaxfield("funcDefAndDecl", "funcDefAndDecl_parameter", TypeProds["variableTermDef"])
    addFieldToProductWithSintaxfield("funcDefAndDecl", "funcDefAndDecl_body", TypeSums["term"])

    SyntaxStructs["funcDefAndDecl_S"] = SyntaxStruct(Array{SyntaxCore}([SyntaxFields["funcDefAndDecl_name"], SyntaxTerms[":"], SyntaxFields["funcDefAndDecl_type"], SyntaxTerms["where"], SyntaxFields["funcDefAndDecl_name"], SyntaxTerms["("], SyntaxFields["funcDefAndDecl_parameter"], SyntaxTerms[")"], SyntaxTerms["="], SyntaxFields["funcDefAndDecl_body"]]))
    bindings[TypeProds["funcDefAndDecl"]] = SyntaxStructs["funcDefAndDecl_S"]


    # //eval sentence
    TypeProds["evalSentence"] = Temp_TypeProd(Array{Temp_Type}([]))

    addFieldToProductWithSintaxfield("evalSentence", "evalSentence_term", TypeSums["term"])

    SyntaxStructs["evalSentence_S"] = SyntaxStruct(Array{SyntaxCore}([ SyntaxTerms["eval"], SyntaxFields["evalSentence_term"]]))
    bindings[TypeProds["evalSentence"]] = SyntaxStructs["evalSentence_S"]


    # //DUMB program, just for show: a program is a funcDefAndDecl, then ";", then an eval:
    TypeProds["program"]=Temp_TypeProd(Array{Temp_Type}([]))

    addFieldToProductWithSintaxfield("program", "program_funcdef", TypeProds["funcDefAndDecl"])
    addFieldToProductWithSintaxfield("program", "program_eval", TypeProds["evalSentence"])

    SyntaxStructs["program_S"] = SyntaxStruct(Array{SyntaxCore}([SyntaxFields["program_funcdef"], SyntaxTerms[";"], SyntaxFields["program_eval"]]))
    bindings[TypeProds["program"]] = SyntaxStructs["program_S"]

    randomParser10 = RandomParser10()

    for (name, s) in SyntaxTerms  addSyntax!(randomParser10.structure.posteriorsStructure, name, s) end
    for (name, s) in SyntaxFields  addSyntax!(randomParser10.structure.posteriorsStructure, name, s) end
    for (name, s) in SyntaxChoicess  addSyntax!(randomParser10.structure.posteriorsStructure, name, s) end
    for (name, s) in SyntaxStructs  addSyntax!(randomParser10.structure.posteriorsStructure, name, s) end
    # for (name, s) in SyntaxStrips  addSyntax!(randomParser10.structure.posteriorsStructure, name, s) end

    d = randomParser10.structure.posteriorsStructure.bindings
    for (s, t) in bindings
        if !(t in keys(d)) d[t] = [s]
        else push!(d[t], s) end
    end

    initializeMarginals(randomParser10.structure.posteriorsStructure)
    initializeChoices(randomParser10.structure.posteriorsStructure)
    # initializeStrips(randomParser10.structure.posteriorsStructure)
    initializePosteriors(randomParser10.structure.posteriorsStructure)

    return randomParser10
end

# randomParser10 = make_s10_big();
# text = "(A->B)-> B";
# parse(randomParser10, text)


# randomParser10 = make_s10_big();
# text = "f:(A->B)-> B";
# parse(randomParser10, text)


# randomParser10 = make_s10_big();
# text = "ff (  g  )  =  g  (  a  )";
# parse(randomParser10, text)


# randomParser10 = make_s10_big();
# text = "ff:A where ff (  g  )  =  a";
# parse(randomParser10, text)
# println("(Btw, length(inputVec) = $(length(randomParser10.inputVec)))")

randomParser10 = make_s10_big();
text = "ff:A->B where ff (  g  )  =  a";
parse(randomParser10, text)
println("(Btw, length(inputVec) = $(length(randomParser10.inputVec)))")


# randomParser10 = make_s10_big();
# text = "ff:(A->B)-> B  where ff (  g  )  =  g  (  a ) ; eval ff ( h ) ";
# parse(randomParser10, text)
# println("(Btw, length(inputVec) = $(length(randomParser10.inputVec)))")


# res = getBestTotalFound(randomParser10)
# if res!==nothing && res isa SyntaxInstStruct
# 	program_S_point = getSyntax(randomParser10.structure.posteriorsStructure, "program_S")
# 	println(res->getSynt(), " ", program_S_point, "\n")
# 	println("K fine\n")
# end



# # //randomParser10.getBestTotalFound.? get.{as SyntaxInstStruct->x | as _->None}.? name.display, WHICH IS OF TYPE: Action + 1, WHATEVER THIS MEANS

S.posteriorsStructure.allSyntaxes["functionType_S_Par"] == obj.s.name




# # int main3()

# # // this is the text you MEAN to use (you just compile it, not parse it):
# text::String = "a:A; (1.a):A+B"

# # // type expession: T = A + ("T -> T") where A is base type and "T -> T" is the function type
# makeNiceTreeStructure("baseTypeVariable", "SumType", "type", "case1", "case2")



hChance.chance|>getString
hChance.object|>trace
hChance.previouses|>length; hChance.previouses[1].object|>trace

hChance.previouses[1].previouses|>length
hChance.previouses[1].previouses[1].object|>trace

hChance.previouses[1].previouses[1].previouses|>length
hChance.previouses[1].previouses[1].previouses[1].object|>trace

hChance.previouses[1].previouses[1].previouses[1].previouses|>length
hChance.previouses[1].previouses[1].previouses[1].previouses[1].object|>trace

hChance.previouses[1].previouses[1].previouses[1].previouses[1].previouses|>length
hChance.previouses[1].previouses[1].previouses[1].previouses[1].previouses[1].object|>trace

hChance.previouses[1].previouses[1].previouses[1].previouses[1].previouses[1].previouses|>length
hChance.previouses[1].previouses[1].previouses[1].previouses[1].previouses[1].previouses[1].object|>trace

hChance.previouses[1].previouses[1].previouses[1].previouses[1].previouses[1].previouses[1].previouses|>length