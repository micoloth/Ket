

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
si = SyntaxInstSimpleString("iii", 1)
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

    addGlobal!(s10p, TGlobAutoCtx("b"))
    s10
end


# request = getInferredTerm(SyntaxInstReference(getType(SyntaxField("first", TypeUniverse())),"A", 0.5))
# request.expr |> pr
# request.type |> pr
# got = rp.structure.finisheds.matrix[1][13] |> x->filter(y->y.s isa SyntaxInstObject, x) |> x->x[1].s.inferred_obj
# got.expr |> pr
# got.type |> pr
# robinsonUnify(got.type.t_out, request.type.t_out; mode=imply_)
# can_be_a(got.type.t_out, request.type.t_out)


s10 = make_s10();
text = "A->B"
rp = RandomParser10("", [], s10);
parse(rp, text)
rp.structure|>trace
getBest(rp.structure)[1] |> (x->trace(x; top=true))

s10 = make_s10();
text = "b"
rp = RandomParser10("", [], s10);
parse(rp, text)
rp.structure|>trace
getBest(rp.structure)[1] |> (x->trace(x; top=true))

s10 = make_s10();
text = "(A->B->C)"
rp = RandomParser10("", [], s10);
parse(rp, text)
rp.structure|>trace
getBest(rp.structure)[1] |> (x->trace(x; top=true))

s10 = make_s10();
text = "((A->B)->B)"
rp = RandomParser10("", [], s10);
parse(rp, text)
rp.structure|>trace
getBest(rp.structure)[1] |> (x->trace(x; top=true))

s10 = make_s10();
text = "g(a)"
rp = RandomParser10("", [], s10);
parse(rp, text)
rp.structure|>trace
getBest(rp.structure)[1] |> (x->trace(x; top=true))

s10 = make_s10();
text = "g(a):B"
rp = RandomParser10("", [], s10);
parse(rp, text)
rp.structure|>trace
getBest(rp.structure)[1] |> (x->trace(x; top=true))

s10 = make_s10();
text = "ff:A where ff (  g  )  =  x"
rp = RandomParser10("", [], s10);
parse(rp, text)
rp.structure|>trace
getBest(rp.structure)[1] |> (x->trace(x; top=true))
println("(Btw, length(inputVec) = $(length(rp.inputVec)))")


s10 = make_s10();
text = "ff:A->B where ff (  g  )  =  b"
rp = RandomParser10("", [], s10);
parse(rp, text)
rp.structure|>trace
getBest(rp.structure)[1] |> (x->trace(x; top=true))

s10 = make_s10();
text = "ff:(A->B)-> B  where ff (  g  )  =  g  (  a ) ; eval ff ( h ) "
rp = RandomParser10("", [], s10);
parse(rp, text)
rp.structure|>trace
getBest(rp.structure)[1] |> (x->trace(x; top=true))







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