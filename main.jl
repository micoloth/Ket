

include("TT/unification_3.jl")
include("TT/mylambda1.jl")
include("Parser/RandomParser10.jl")

s = SyntaxTerm("+")
si = SyntaxInstTerm(s, 1)
s = SyntaxChoice([s, s])
si = SyntaxInstChoice(s, 0, si, 1)
s = SyntaxStruct([s,s])
si = SyntaxInstStruct(s, [si, si], 1)
s = SyntaxField("first", TGlob("A"))
si = SyntaxInstReference(TGlob("A"), "a", 1)
si = SyntaxInstNativeString("iii", 1)
si = SyntaxInstObject(si, 1, TAnno(TGlob("A"), TypeUniverse()))
si = SyntaxInstField(s, si, 1)
# s = SyntaxStrip()
# si = SyntaxInstStrip()

# fs = FinishedsStructure10(3); fs|>trace
# getS(s) = SyntaxInstOwner(SyntaxInstTerm(SyntaxTerm(s), 1))

# fs = FinishedsStructure10([getS("+"), getS("-"), getS(":")]); fs|>trace
# reshape(fs, 0, 1, 1); fs|>trace
# reshape(fs, 0, 0, 1); fs|>trace
# reshape(fs, 0, 1, 0); fs|>trace
# reshape(fs, 0, 2, 3); fs|>trace
# reshape(fs, 0, 2, 2); fs|>trace

# reshape(fs, 3, 3, 1); fs|>trace
# reshape(fs, 2, 3, 3); fs|>trace
# reshape(fs, 2, 3, 0); fs|>trace
# reshape(fs, 3, 3, 2); fs|>trace

# fs = FinishedsStructure10([getS("+"), getS("-"), getS(":")]); fs|>trace
# set(fs, 0,2,[getS("+-")]); fs|>trace
# @assert [s for s in IterableForElementsEndingAt(fs.matrix, 1)] |> length == 1
# @assert [s for s in IterableForElementsEndingAt(fs.matrix, 2)] |> length == 2
# @assert [s for s in IterableForElementsEndingAt(fs.matrix, 3)] |> length == 1
# @assert [s for s in IterableForElementsStartingFrom(fs.matrix, 0)] |> length == 2
# @assert [s for s in IterableForElementsStartingFrom(fs.matrix, 1)] |> length == 1
# @assert [s for s in IterableForElementsStartingFrom(fs.matrix, 2)] |> length == 1


# # OK!^

# get_hc_beg(s::String) = HangingChance10(
#     SyntaxStruct([SyntaxTerm(s),SyntaxTerm("=")]),
#     SyntaxInstTerm(SyntaxTerm(s), 1),
#     0, 1,
#     1, 1)
# get_hc_beg("+")
# get_hc_end(s::String) = HangingChance10(
#     SyntaxStruct([SyntaxTerm("+"),SyntaxTerm(s)]),
#     SyntaxInstTerm(SyntaxTerm(s), 1),
#     1, 1,
#     1, 1)
# get_hc_end("+")

# function get_cs()
#     cs = ChancesStructure10()
#     reshape(cs, 0,0,3)
#     addBeginning(cs, get_hc_beg("+"), 1)
#     addBeginning(cs, get_hc_beg("+"), 1)
#     addEnding(cs, get_hc_end("="), 1)
#     addEnding(cs, get_hc_end("="), 2)
#     println(cs.beginnings.|>length), println(cs.endings.|>length);
#     cs
# end

# cs = get_cs();

# # reshape(cs, 0,1,0); println(cs.beginnings.|>length), println(cs.endings.|>length);# YES
# # reshape(cs, 0,0,1); println(cs.beginnings.|>length), println(cs.endings.|>length);# deleting too much
# # reshape(cs, 0,1,1); println(cs.beginnings.|>length), println(cs.endings.|>length);# YES

# # reshape(cs, 2,3,0); println(cs.beginnings.|>length), println(cs.endings.|>length);# YES
# # reshape(cs, 2,3,2); println(cs.beginnings.|>length), println(cs.endings.|>length);# YES
# # reshape(cs, 3,3,2); println(cs.beginnings.|>length), println(cs.endings.|>length);# YES



# ########## Parsing 1: Parse "+"

# s10 = Structure11()
# addSyntax!(s10.posteriorsStructure, "+", SyntaxTerm("+"))
# initializeMarginals(s10.posteriorsStructure)
# initializeChoices(s10.posteriorsStructure)
# initializePosteriors(s10.posteriorsStructure)
# # initializeStrips(s10.posteriorsStructure)

# insertTerminal(s10, 0,1,SyntaxTerm("+"), 1)
# s10.finisheds|>trace
# doTheBestYouCan(s10)
# s10.finisheds|>trace


# s10 = Structure11()
# rp = RandomParser10("", [], s10)
# parse(rp, "+")
# rp.structure|>trace



# ########## Parsing 2: Parse "->"

# s10 = Structure11()

# SyntaxTerms = Dict{String, SyntaxTerm}()
# SyntaxFields = Dict{String, SyntaxField}()
# SyntaxChoicess = Dict{String, SyntaxChoice}()
# SyntaxStructs = Dict{String, SyntaxStruct}()
# SyntaxStrips = Dict{String, SyntaxStrip}()
# TypeBases = Dict{String, TGlob}()
# TypeFuncs = Dict{String, Term}()
# TypeSums = Dict{String, TSum}()
# TypeProds = Dict{String, TProd}()
# bindings = Dict{Term, SyntaxCore}()

# for i in ["{", "-",">"] SyntaxTerms[i] =SyntaxTerm(i) end
# SyntaxStructs["arrow"] = SyntaxStruct(Array{SyntaxCore}([SyntaxTerms["-"], SyntaxTerms[">"]]))
# SyntaxChoicess["arrow_S"] = SyntaxChoice(Array{SyntaxCore}([SyntaxStructs["arrow"]]))

# for (name, s) in SyntaxTerms  addSyntax!(s10.posteriorsStructure, name, s) end
# for (name, s) in SyntaxChoicess  addSyntax!(s10.posteriorsStructure, name, s) end
# for (name, s) in SyntaxStructs  addSyntax!(s10.posteriorsStructure, name, s) end
# initializeMarginals(s10.posteriorsStructure)
# initializeChoices(s10.posteriorsStructure)
# initializePosteriors(s10.posteriorsStructure)


# text = "->"

# rp = RandomParser10("", [], s10);
# parse(rp, text)
# rp.structure|>trace



########## Parsing 3: Parse "A->B"

# function typearrow_builder(d::Dict{String, TAnno})::TAnno
#     build_anno_term_TTerm(d["first"], d["second"]; make_auto=true)
# end
function typearrow_builder_strip(d::Array{TAnno})::TAnno
    foldr(build_anno_term_TTerm, d)
end
function typearrow_builder_inpar(d::Dict{String, TAnno})::TAnno
    d["typearrow_inpar"] # It should ALREADY be a TAnno... ^
end
function funcapp_builder(d::Dict{String, TAnno})::TAnno
    build_anno_term_TApp([d["arg"], d["func"]])
end
function tannotation_builder(d::Dict{String, TAnno})::TAnno
    build_anno_term_TAnno(d["anno_obj"], d["anno_type"])
end
function typedef_builder(d::Dict{String, TAnno})::TAnno # For the :Type" syntax
    if d["typename"].type.t_out !==TypeUniverse()
        throw(DomainError("Whats going on here ???????? with term $(d["typename"]|>pr) written to be : \"Type\", but it didnt come out as a TypeUniverse at all, tho ..."))
    end
    d["typename"] # It should ALREADY be a TAnno... ^
end
function funcdecl_builder(d::Dict{String, TAnno})::TAnno
    types = Array{TTerm}([d["name"].type, d["type"].type, d["name2"].type, d["parameter"].type, d["body"].type])
    if types[1].t_out !== TS()# Wait.... Havent you ALREADY checked this tho ??????????
        throw(DomainError("Whats going on here ???????? with function name $(d["name"]|>pr) which is def not a String ...")) end
    if (d["parameter"].expr isa TStr) # Wait.. WHat's the difference ????? ^
        throw(DomainError("Why is param not a TStr ??? > $(d["parameter"]|>pr)")) end
    if types[2].t_out !== TypeUniverse()# Wait.... Havent you ALREADY checked this tho ??????????
        throw(DomainError("Whats going on here ???????? with function type $(d["name"]|>pr) which is def not a TypeUniverse ...")) end
    # if !(d["type"].expr isa TTerm) # Should be Can be a  # Wait.... Havent you ALREADY checked this tho ??????????
    #     throw(DomainError("Whats going on here ???????? with function type $(d["type"]|>pr) which is def not a TTerm ...")) end
    # if d["type"].expr.t_in.data |> length !=0
    #     throw(DomainError("I dont even know how, but you inferred a TTerm w/ unnamed vars: $(d["type"].expr.t_in|>pr)")) end
    # if !(d["parameter"].expr.s in keys(d["type"].expr.t_in.data_tags))
    #     throw(DomainError("The function param should be in the func arg type names: $(d["parameter"]|>pr) not in $(d["type"].expr.t_in|>pr)")) end
    if d["name"].expr != d["name2"].expr
        throw(DomainError("The What are you even writing? These don't match... $(d["name"]|>pr) != $(d["name2"]|>pr)")) end
    build_anno_term_TAnno(build_anno_term_TAbs(d["body"]), d["type"])
end

function evalterm_builder(d::Dict{String, TAnno})::TAnno
    res = TSumTerm(1, "to_eval", d["evalSentence_term"].expr)
    return TAnno(res, infer_type_(res, d["evalSentence_term"].type))
end

function fullprog_builder(d::Dict{String, TAnno})::TAnno
    res = TProd([d["program_funcdef"].expr, d["program_eval"].expr])
    return TAnno(res, infer_type_(res, d["program_funcdef"].type, d["program_eval"].type))
end

# function references_handler(d::Array{Dict})



function make_s10()
    s10 = Structure11()

    SyntaxTerms = Dict{String, SyntaxTerm}()
    SyntaxFields = Dict{String, SyntaxField}()
    SyntaxChoicess = Dict{String, SyntaxChoice}()
    SyntaxStructs = Dict{String, SyntaxStruct}()
    SyntaxStrips = Dict{String, SyntaxStrip}()
    TypeBases = Dict{String, TGlob}()
    TypeFuncs = Dict{String, Term}()
    TypeSums = Dict{String, TSum}()
    TypeProds = Dict{String, TProd}()
    bindings = Dict{Term, SyntaxCore}()

    for i in ["{", "-",">",":","=","(",")",";","where","Type","eval","}"] SyntaxTerms[i] =SyntaxTerm(i) end
    SyntaxStructs["arrow"] = SyntaxStruct(Array{SyntaxCore}([SyntaxTerms["-"], SyntaxTerms[">"]]))
    # SyntaxChoicess["arrow_S"] = SyntaxChoice(Array{SyntaxCore}([SyntaxStructs["arrow"]]))

    function auto_SyntStruct(ss::Array{Union{String, SyntaxCore}})
        for (i, s) in enumerate(ss)
            if s isa SyntaxField
                SyntaxFields[s.name] = s
                ss[i] = SyntaxFields[s.name]  # In Julia this is prob exactly the same, but i want ref equality
            elseif s isa String
                SyntaxTerms[s] = SyntaxTerm(s)
                ss[i] = SyntaxTerms[s]  # In Julia this is prob exactly the same, but i want ref equality
        end end
        SyntaxStruct(ss)
    end
    function auto_SyntStrip(ssb::Union{String, SyntaxCore, Nothing}, sso::Union{String, SyntaxCore}, ssc::Union{String, SyntaxCore}, ssa::Union{String, SyntaxCore, Nothing})
        dd = Dict("ssb"=> ssb,"sso"=> sso,"ssc"=> ssc,"ssa"=> ssa,)
        for (n, s) in dd
            if s isa SyntaxField
            SyntaxFields[s.name] = s
            dd[n] = s  # In Julia this is prob exactly the same, but i want ref equality
        elseif s isa String
            SyntaxTerms[s] = SyntaxTerm(s)
            dd[n] = SyntaxTerms[s]  # In Julia this is prob exactly the same, but i want ref equality
        end end
        SyntaxStrip(dd["ssb"], dd["sso"], dd["ssc"], dd["ssa"])
    end
    AUSS = Array{Union{String, SyntaxCore}}

    # SyntaxStructs["typearrow_nopar"] = auto_SyntStruct(AUSS[SyntaxField("first", TypeUniverse()), SyntaxStructs["arrow"], SyntaxField("second", TypeUniverse())])
    SyntaxStrips["typearrow_strip"] = auto_SyntStrip(nothing, SyntaxField("typearrow_first", TypeUniverse()), SyntaxStructs["arrow"], nothing)
    SyntaxStructs["typearrow_par"] = auto_SyntStruct(AUSS(["(", SyntaxField("typearrow_inpar", TypeUniverse()), ")"]))
    SyntaxChoicess["typearrow"] = SyntaxChoice(Array{SyntaxCore}([SyntaxStructs["typearrow_par"], SyntaxStrips["typearrow_strip"]]))

    SyntaxStructs["funcApp_S"] = auto_SyntStruct(AUSS([SyntaxField("func", TTerm(TLocInt(1), TLocInt(2))), "(", SyntaxField("arg", TLocInt(1)), ")"]))
    SyntaxStructs["BaseTypeDef_S"] = auto_SyntStruct(AUSS([SyntaxField("tname", TS()), ":", "Type"]))
    SyntaxStructs["termanno_S"] = auto_SyntStruct(AUSS([SyntaxField("anno_obj", TLocInt(1)), ":", SyntaxField("anno_type", TypeUniverse())]))
    SyntaxStructs["funcDefAndDecl_S"] = auto_SyntStruct(AUSS([SyntaxField("name", TS()), ":", SyntaxField("type", TypeUniverse()), "where", SyntaxField("name2", TS()), "(", SyntaxField("parameter", TS()), ")", "=", SyntaxField("body", TLocInt(1))]))
    SyntaxFields["evalSentence_term"] = SyntaxField("term_toeval", TLocInt(1))
    SyntaxStructs["evalSentence_S"] = auto_SyntStruct(AUSS(["eval", SyntaxFields["evalSentence_term"]]))
    SyntaxStructs["program_S"] = auto_SyntStruct(AUSS([SyntaxField("program_funcdef", TLocInt(1)), ";", SyntaxField("program_eval", TLocInt(1))]))

    s10p = s10.posteriorsStructure
    for (name, s) in SyntaxTerms  addSyntax!(s10p, name, s) end
    for (name, s) in SyntaxChoicess  addSyntax!(s10p, name, s) end
    for (name, s) in SyntaxStructs  addSyntax!(s10p, name, s) end
    for (name, s) in SyntaxStrips  addSyntax!(s10p, name, s) end
    for (name, s) in SyntaxFields  addSyntax!(s10p, name, s) end
    initializeMarginals(s10p)
    initializeChoices(s10p)
    initializePosteriors(s10p)

    # s10p.bindings[s10p.allSyntaxes["typearrow"]] = [typearrow_builder_strip]
    s10p.bindings[s10p.allSyntaxes["typearrow"]] =[ Array([typearrow_builder_inpar, typearrow_builder_strip])]
    s10p.bindings[s10p.allSyntaxes["funcApp_S"]] = [funcapp_builder]
    s10p.bindings[s10p.allSyntaxes["BaseTypeDef_S"]] = [typedef_builder]
    s10p.bindings[s10p.allSyntaxes["termanno_S"]] = [tannotation_builder]
    s10p.bindings[s10p.allSyntaxes["funcDefAndDecl_S"]] = [funcdecl_builder]
    s10p.bindings[s10p.allSyntaxes["evalSentence_S"]] = [evalterm_builder]
    s10p.bindings[s10p.allSyntaxes["program_S"]] = [fullprog_builder]

    s10
end


# request = getInferredTerm(SyntaxInstReference(getType(SyntaxField("first", TypeUniverse())),"A", 0.5))
# request.expr |> pr
# request.type |> pr
# got = rp.structure.finisheds.matrix[1][13] |> x->filter(y->y.s isa SyntaxInstObject, x) |> x->x[1].s.inferred_obj
# got.expr |> pr
# got.type |> pr


robinsonUnify(got.type.t_out, request.type.t_out; mode=imply_)
can_be_a(got.type.t_out, request.type.t_out)

s10 = make_s10();
text = "A->B"
rp = RandomParser10("", [], s10);
parse(rp, text)
rp.structure|>trace

s10 = make_s10();
text = "(A->B->C)"
rp = RandomParser10("", [], s10);
parse(rp, text)
rp.structure|>trace

s10 = make_s10();
text = "((A->B)->B)"
rp = RandomParser10("", [], s10);
parse(rp, text)
rp.structure|>trace

s10 = make_s10();
text = "g(a)"
rp = RandomParser10("", [], s10);
parse(rp, text)
rp.structure|>trace

s10 = make_s10();
text = "g(a):B"
rp = RandomParser10("", [], s10);
parse(rp, text)
rp.structure|>trace

s10 = make_s10();
text = "ff:A where ff (  g  )  =  x"
rp = RandomParser10("", [], s10);
parse(rp, text)
rp.structure|>trace
println("(Btw, length(inputVec) = $(length(rp.inputVec)))")


s10 = make_s10();
text = "ff:A->B where ff (  g  )  =  b"
rp = RandomParser10("", [], s10);
parse(rp, text)
rp.structure|>trace

s10 = make_s10();
text = "ff:(A->B)-> B  where ff (  g  )  =  g  (  a ) ; eval ff ( h ) "
rp = RandomParser10("", [], s10);
parse(rp, text)
rp.structure|>trace




########## Parsing 4: Parse The original example!!

function make_s10_big()

    SyntaxTerms = Dict{String, SyntaxTerm}()
    SyntaxFields = Dict{String, SyntaxField}()
    SyntaxChoicess = Dict{String, SyntaxChoice}()
    SyntaxStructs = Dict{String, SyntaxStruct}()
    SyntaxStrips = Dict{String, SyntaxStrip}()

    TypeBases = Dict{String, TGlob}()
    TypeFuncs = Dict{String, TTerm}()
    TypeSums = Dict{String, TSum}()
    TypeProds = Dict{String, TProd}()

    bindings = Dict{Term, SyntaxCore}()

    # //base words
    for i in ["{", "-",">",":","=","(",")",";","where","Type","eval","}"]
        SyntaxTerms[i] =SyntaxTerm(i)
    end


    function addFieldToProductWithSintaxfield(whichProduct::String, fieldName::String, whichField::Term)
        ######################### NOTE: This prod has STR NAMES associated w/ fields, ALREADY!!!
        push!(TypeProds[whichProduct].data, whichField)
        push!(TypeProds[whichProduct].tags, fieldName)
        SyntaxFields[fieldName] = SyntaxField(fieldName, whichField)
    end

    function makeNiceTreeStructure(leafName::String, productBranchName::String, sumName::String, fieldNameFirst::String, FieldNameSecond::String)
        # //creates a nice tree that is made like this: T = A + (T x T) where A is a TGlob with a name

        TypeBases[leafName] = TGlob(leafName)
        TypeProds[productBranchName] = TProd(Array{Term}([]))
        TypeSums[sumName] = TSum([TypeProds[productBranchName], TypeBases[leafName] ])

        ######################### NOTE: This prod has STR NAMES associated w/ fields, ALREADY!!!
        addFieldToProductWithSintaxfield(productBranchName, fieldNameFirst, TypeSums[sumName])
        addFieldToProductWithSintaxfield(productBranchName, FieldNameSecond, TypeSums[sumName])
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
    TypeProds["baseTypeDef"] = TProd(Array{Term}([]))

    # ///ALSO I'M _REALLY_ NOT SURE ABOUT THE NEXT LINES.........................
    addFieldToProductWithSintaxfield("baseTypeDef", "BaseTypeDef_name", TypeBases["baseTypeVariable"])

    SyntaxStructs["BaseTypeDef_S"] = SyntaxStruct(Array{SyntaxCore}([SyntaxFields["BaseTypeDef_name"], SyntaxTerms[":"], SyntaxTerms["Type"]]))
    bindings[TypeProds["baseTypeDef"]] = SyntaxStructs["BaseTypeDef_S"]


    # //term def: syntax "a: T" where a is the name of the variable and T is a type
    TypeProds["variableTermDef"] = TProd(Array{Term}([]))

    addFieldToProductWithSintaxfield("variableTermDef", "variableTermDef_name", TypeBases["variable"])
    addFieldToProductWithSintaxfield("variableTermDef", "variableTermDef_type", TypeSums["type"])

    SyntaxStructs["variableTermDef_S"] = SyntaxStruct(Array{SyntaxCore}([SyntaxFields["variableTermDef_name"], SyntaxTerms[":"], SyntaxFields["variableTermDef_type"]]))
    bindings[TypeProds["variableTermDef"]] = SyntaxStructs["variableTermDef_S"]


    # //funcion definition and declaration:
    # //syntax "f: T where f(x)={t}" where f is the function name, T is a type, and t is a term.
    TypeProds["funcDefAndDecl"] = TProd(Array{Term}([]))

    addFieldToProductWithSintaxfield("funcDefAndDecl", "funcDefAndDecl_name", TypeBases["variable"])
    addFieldToProductWithSintaxfield("funcDefAndDecl", "funcDefAndDecl_type", TypeSums["type"])
    addFieldToProductWithSintaxfield("funcDefAndDecl", "funcDefAndDecl_parameter", TypeProds["variableTermDef"])
    addFieldToProductWithSintaxfield("funcDefAndDecl", "funcDefAndDecl_body", TypeSums["term"])

    SyntaxStructs["funcDefAndDecl_S"] = SyntaxStruct(Array{SyntaxCore}([SyntaxFields["funcDefAndDecl_name"], SyntaxTerms[":"], SyntaxFields["funcDefAndDecl_type"], SyntaxTerms["where"], SyntaxFields["funcDefAndDecl_name"], SyntaxTerms["("], SyntaxFields["funcDefAndDecl_parameter"], SyntaxTerms[")"], SyntaxTerms["="], SyntaxFields["funcDefAndDecl_body"]]))
    bindings[TypeProds["funcDefAndDecl"]] = SyntaxStructs["funcDefAndDecl_S"]


    # //eval sentence
    TypeProds["evalSentence"] = TProd(Array{Term}([]))

    addFieldToProductWithSintaxfield("evalSentence", "evalSentence_term", TypeSums["term"])

    SyntaxStructs["evalSentence_S"] = SyntaxStruct(Array{SyntaxCore}([ SyntaxTerms["eval"], SyntaxFields["evalSentence_term"]]))
    bindings[TypeProds["evalSentence"]] = SyntaxStructs["evalSentence_S"]


    # //DUMB program, just for show: a program is a funcDefAndDecl, then ";", then an eval:
    TypeProds["program"]=TProd(Array{Term}([]))

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


randomParser10 = make_s10_big();
text = "g  (  a  )";
parse(randomParser10, text)

randomParser10 = make_s10_big();
text = "ff (  g  )  =  g  (  a  )";
parse(randomParser10, text)

randomParser10 = make_s10_big();
text = "(A->B)-> B";
parse(randomParser10, text)


randomParser10 = make_s10_big();
text = "f:(A->B)-> B";
parse(randomParser10, text)


randomParser10 = make_s10_big();
text = "ff:A where ff (  g  )  =  a";
parse(randomParser10, text)
println("(Btw, length(inputVec) = $(length(randomParser10.inputVec)))")

randomParser10 = make_s10_big();
text = "ff:A->B where ff (  g  )  =  a";
parse(randomParser10, text)
println("(Btw, length(inputVec) = $(length(randomParser10.inputVec)))")


randomParser10 = make_s10_big();
text = "ff:(A->B)-> B  where ff (  g  )  =  g  (  a ) ; eval ff ( h ) ";
parse(randomParser10, text)
println("(Btw, length(inputVec) = $(length(randomParser10.inputVec)))")


getBestTotalFound(randomParser10).s.syntax
SyntaxInstObject





# uhuhuhuhuhuhuhuhuhuhuhuhuh mnmnmnmnmnmnmnmnmnmnmmmmnmmmnmnmnmnmnmnmnmnmnm
# ahahahahahahahahahahahahahahahahahahahahahahahahahahahahahahahahahahahaha

# res = getBestTotalFound(randomParser10)
# if res!==nothing && res isa SyntaxInstStruct
# 	program_S_point = getSyntax(randomParser10.structure.posteriorsStructure, "program_S")
# 	println(res->getSynt(), " ", program_S_point, "\n")
# 	println("K fine\n")
# end






function add!(dict_of_arrays, key, obj)
    if !(key in keys(dict_of_arrays)) dict_of_arrays[key] = [obj]
    else push!(dict_of_arrays[key], obj) end
end


function make_s10_new()

    SyntaxTerms = Dict{String, SyntaxTerm}()
    SyntaxFields = Dict{String, SyntaxField}()
    SyntaxChoicess = Dict{String, SyntaxChoice}()
    SyntaxStructs = Dict{String, SyntaxStruct}()
    SyntaxStrips = Dict{String, SyntaxStrip}()

    TypeBases = Dict{String, TGlob}()
    TypeFuncs = Dict{String, TTerm}()
    TypeSums = Dict{String, TSum}()
    TypeProds = Dict{String, TProd}()

    bindings = Dict{SyntaxCore, Array{Any}}() # Any is a (Dict{String, Union{Term,Error}}) -> Union{TAnno, Error}  lambda !!!

    # //base words
    for i in ["{", "-",">",":","=","(",")",";","where","Type","eval","}"]
        SyntaxTerms[i] =SyntaxTerm(i)
    end


    function addFieldToProductWithSintaxfield(whichProduct::String, fieldName::String, whichField::Term)
        ######################### NOTE: This prod has STR NAMES associated w/ fields, ALREADY!!!
        push!(TypeProds[whichProduct].data, whichField)
        push!(TypeProds[whichProduct].tags, fieldName)
        SyntaxFields[fieldName] = SyntaxField(fieldName, whichField)
    end

    function makeNiceTreeStructure(leafName::String, productBranchName::String, sumName::String, fieldNameFirst::String, FieldNameSecond::String)
        # //creates a nice tree that is made like this: T = A + (T x T) where A is a TGlob with a name

        TypeBases[leafName] = TGlob(leafName)
        TypeProds[productBranchName] = TProd(Array{Term}([]))
        TypeSums[sumName] = TSum([TypeProds[productBranchName], TypeBases[leafName] ])

        ######################### NOTE: This prod has STR NAMES associated w/ fields, ALREADY!!!
        addFieldToProductWithSintaxfield(productBranchName, fieldNameFirst, TypeSums[sumName])
        addFieldToProductWithSintaxfield(productBranchName, FieldNameSecond, TypeSums[sumName])
    end




    # // type expession: T = A + ("T -> T") where A is base type and "T -> T" is the function type
    makeNiceTreeStructure("baseTypeVariable", "functionType", "type", "first", "second");

    SyntaxStructs["functionType_S_noPar"] = SyntaxStruct(Array{SyntaxCore}([SyntaxFields["first"], SyntaxTerms["-"], SyntaxTerms[">"], SyntaxFields["second"]]))
    SyntaxStructs["functionType_S_Par"] = SyntaxStruct(Array{SyntaxCore}([SyntaxTerms["("], SyntaxStructs["functionType_S_noPar"], SyntaxTerms[")"]]))
    SyntaxChoicess["functionType_S"] = SyntaxChoice(Array{SyntaxCore}([SyntaxStructs["functionType_S_Par"], SyntaxStructs["functionType_S_noPar"]]))

    build_functionType = (x::Dict{String, Union{Term,Error}}->TAnno(TTerm(x["first"], x["second"]), TypeUniverse()))
    add!(bindings, SyntaxChoicess["functionType_S"], build_functionType) # //it HAS BEEN:  << SyntaxChoicess.getSyntaxCore("functionType_S_Par_noPar");



    # # //terms expression: t = a + "t(t)" where a is a variable and t(t) is a function application
    # makeNiceTreeStructure("variable", "funcApp", "term", "func", "arg")#//FINALLY, FUOND WHERE IT BREAKS
    #                                                                     #	//this DOES NOT SURPRISE US
    #                                                                     #	//this, WAS ABOUT TIME

    # SyntaxStructs["funcApp_S"] = SyntaxStruct(Array{SyntaxCore}([SyntaxFields["func"], SyntaxTerms["("], SyntaxFields["arg"], SyntaxTerms[")"]]))
    # bindings[TypeProds["funcApp"]] = SyntaxStructs["funcApp_S"]

    # # //// ok

    # # //base type def: syntax "A: Type" where A is the name of the type
    # TypeProds["baseTypeDef"] = TProd(Array{Term}([]))

    # # ///ALSO I'M _REALLY_ NOT SURE ABOUT THE NEXT LINES.........................
    # addFieldToProductWithSintaxfield("baseTypeDef", "BaseTypeDef_name", TypeBases["baseTypeVariable"])

    # SyntaxStructs["BaseTypeDef_S"] = SyntaxStruct(Array{SyntaxCore}([SyntaxFields["BaseTypeDef_name"], SyntaxTerms[":"], SyntaxTerms["Type"]]))
    # bindings[TypeProds["baseTypeDef"]] = SyntaxStructs["BaseTypeDef_S"]


    # # //term def: syntax "a: T" where a is the name of the variable and T is a type
    # TypeProds["variableTermDef"] = TProd(Array{Term}([]))

    # addFieldToProductWithSintaxfield("variableTermDef", "variableTermDef_name", TypeBases["variable"])
    # addFieldToProductWithSintaxfield("variableTermDef", "variableTermDef_type", TypeSums["type"])

    # SyntaxStructs["variableTermDef_S"] = SyntaxStruct(Array{SyntaxCore}([SyntaxFields["variableTermDef_name"], SyntaxTerms[":"], SyntaxFields["variableTermDef_type"]]))
    # bindings[TypeProds["variableTermDef"]] = SyntaxStructs["variableTermDef_S"]


    # # //funcion definition and declaration:
    # # //syntax "f: T where f(x)={t}" where f is the function name, T is a type, and t is a term.
    # TypeProds["funcDefAndDecl"] = TProd(Array{Term}([]))

    # addFieldToProductWithSintaxfield("funcDefAndDecl", "funcDefAndDecl_name", TypeBases["variable"])
    # addFieldToProductWithSintaxfield("funcDefAndDecl", "funcDefAndDecl_type", TypeSums["type"])
    # addFieldToProductWithSintaxfield("funcDefAndDecl", "funcDefAndDecl_parameter", TypeProds["variableTermDef"])
    # addFieldToProductWithSintaxfield("funcDefAndDecl", "funcDefAndDecl_body", TypeSums["term"])

    # SyntaxStructs["funcDefAndDecl_S"] = SyntaxStruct(Array{SyntaxCore}([SyntaxFields["funcDefAndDecl_name"], SyntaxTerms[":"], SyntaxFields["funcDefAndDecl_type"], SyntaxTerms["where"], SyntaxFields["funcDefAndDecl_name"], SyntaxTerms["("], SyntaxFields["funcDefAndDecl_parameter"], SyntaxTerms[")"], SyntaxTerms["="], SyntaxFields["funcDefAndDecl_body"]]))
    # bindings[TypeProds["funcDefAndDecl"]] = SyntaxStructs["funcDefAndDecl_S"]


    # # //eval sentence
    # TypeProds["evalSentence"] = TProd(Array{Term}([]))

    # addFieldToProductWithSintaxfield("evalSentence", "evalSentence_term", TypeSums["term"])

    # SyntaxStructs["evalSentence_S"] = SyntaxStruct(Array{SyntaxCore}([ SyntaxTerms["eval"], SyntaxFields["evalSentence_term"]]))
    # bindings[TypeProds["evalSentence"]] = SyntaxStructs["evalSentence_S"]


    # # //DUMB program, just for show: a program is a funcDefAndDecl, then ";", then an eval:
    # TypeProds["program"]=TProd(Array{Term}([]))

    # addFieldToProductWithSintaxfield("program", "program_funcdef", TypeProds["funcDefAndDecl"])
    # addFieldToProductWithSintaxfield("program", "program_eval", TypeProds["evalSentence"])

    # SyntaxStructs["program_S"] = SyntaxStruct(Array{SyntaxCore}([SyntaxFields["program_funcdef"], SyntaxTerms[";"], SyntaxFields["program_eval"]]))
    # bindings[TypeProds["program"]] = SyntaxStructs["program_S"]

    randomParser10 = RandomParser10()

    for (name, s) in SyntaxTerms  addSyntax!(randomParser10.structure.posteriorsStructure, name, s) end
    for (name, s) in SyntaxFields  addSyntax!(randomParser10.structure.posteriorsStructure, name, s) end
    for (name, s) in SyntaxChoicess  addSyntax!(randomParser10.structure.posteriorsStructure, name, s) end
    for (name, s) in SyntaxStructs  addSyntax!(randomParser10.structure.posteriorsStructure, name, s) end
    # for (name, s) in SyntaxStrips  addSyntax!(randomParser10.structure.posteriorsStructure, name, s) end

    randomParser10.structure.posteriorsStructure.bindings = bindings

    initializeMarginals(randomParser10.structure.posteriorsStructure)
    initializeChoices(randomParser10.structure.posteriorsStructure)
    # initializeStrips(randomParser10.structure.posteriorsStructure)
    initializePosteriors(randomParser10.structure.posteriorsStructure)

    return randomParser10
end


randomParser10 = make_s10_new();
text = "A->B";
parse(randomParser10, text)

randomParser10 = make_s10_new();
text = "(A->B)-> B";
parse(randomParser10, text)

randomParser10 = make_s10_new();
text = "g  (  a  )";
parse(randomParser10, text)

randomParser10 = make_s10_new();
text = "ff (  g  )  =  g  (  a  )";
parse(randomParser10, text)

randomParser10 = make_s10_new();
text = "f:(A->B)-> B";
parse(randomParser10, text)

randomParser10 = make_s10_new();
text = "ff:A where ff (  g  )  =  a";
parse(randomParser10, text)
println("(Btw, length(inputVec) = $(length(randomParser10.inputVec)))")

randomParser10 = make_s10_new();
text = "ff:A->B where ff (  g  )  =  a";
parse(randomParser10, text)
println("(Btw, length(inputVec) = $(length(randomParser10.inputVec)))")


randomParser10 = make_s10_new();
text = "ff:(A->B)-> B  where ff (  g  )  =  g  (  a ) ; eval ff ( h ) ";
parse(randomParser10, text)
println("(Btw, length(inputVec) = $(length(randomParser10.inputVec)))")




# # //randomParser10.getBestTotalFound.? get.{as SyntaxInstStruct->x | as _->None}.? name.display, WHICH IS OF TYPE: Action + 1, WHATEVER THIS MEANS




# # int main3()

# # // this is the text you MEAN to use (you just compile it, not parse it):
# text::String = "a:A; (1.a):A+B"

# # // type expession: T = A + ("T -> T") where A is base type and "T -> T" is the function type
# makeNiceTreeStructure("baseTypeVariable", "SumType", "type", "case1", "case2")



# hChance.chance|>getString
# hChance.object|>trace
# hChance.previouses|>length; hChance.previouses[1].object|>trace

# hChance.previouses[1].previouses|>length
# hChance.previouses[1].previouses[1].object|>trace

# hChance.previouses[1].previouses[1].previouses|>length
# hChance.previouses[1].previouses[1].previouses[1].object|>trace

# hChance.previouses[1].previouses[1].previouses[1].previouses|>length
# hChance.previouses[1].previouses[1].previouses[1].previouses[1].object|>trace

# hChance.previouses[1].previouses[1].previouses[1].previouses[1].previouses|>length
# hChance.previouses[1].previouses[1].previouses[1].previouses[1].previouses[1].object|>trace

# hChance.previouses[1].previouses[1].previouses[1].previouses[1].previouses[1].previouses|>length
# hChance.previouses[1].previouses[1].previouses[1].previouses[1].previouses[1].previouses[1].object|>trace

# hChance.previouses[1].previouses[1].previouses[1].previouses[1].previouses[1].previouses[1].previouses|>length