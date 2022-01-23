
**Ket** is (a very WIP demo for what I think should be) a **Computer Assisted Programming or CAP** (like designers have Compute Assisted Design or CAD) **framework**.

The idea behind Ket is that **software development could be 10x faster**, and hence 10x cheaper, than it currently is, if we delegate to the computer the accidentally complex parts of this job.

I’m convinced that if looked from the right angle, 90% of the daily job of a modern programmer is accidental complexity.
The idea is that that’s software engineers, we should (wait for it) let software do the accidentally complex parts of this job, not taking pride in doing them ourselves.

A Computed Assisted Programming framework is a coding frontend that wraps a type system, **a theorem prover** (for code generation), **an incremental parser** (for powerful hints) **and a dependency system** to make building software fast and enjoyable.

# Ket will be based on these principles:
- **Doing things the Right Way** (as opposed to some hacks to achieve something quicker) **will be Good in the long run**. Or Slow is right, and Right is fast. Except that, software engineering Doesn't have to be slow to be right. That’s only true without proper tooling.
- There’s an idea that strongly typed languages are good for their correctness and safety, even if that comes at the expense of productivity. But that’s nonsense. **Good (strongly typed) languages should be good *for their productivity***. You know what is productive? Not having to debug at runtime is productive. Automatic code generation is productive. Powerful refactoring utilities are productive. \
Of course, none of the strongly typed languages are very productive *today*. Ket is exactly an attempt to change that.
- As it is well known, code generation and theorem proving are the same thing. **A powerful, expressive type inference and code generation tool should be powered by a smart theorem prover**.
- **Incremental typechecking is Good**.
- **Flexible, incremental parsing is Good**. Parsing the code incrementally while it's written instead of reparsing the whole codebase at every keystroke is harder and theoretically much more inefficient, but it's much more ergonomic for the programmer, and modern computers are more than powerful enough to do it.
- **Incremental, Jitted compilation**
- **Reactive execution** (like in the [Pluto notebooks](https://github.com/fonsp/Pluto.jl) recently, and many other places before), because thus is the right way of building software.
- **(controlled) Incremental execution**: many compilers have compile time code execution, and I’m sure that many other compile time executions are performed implicitly as optimization passes. This is Good and nice, but it should be Controllable, Explicit, and still Seamless so that making the right decision (whether to compile time execute or not) is effortless and natural.
- **Macros are a terrible idea**. When the previous point is properly implemented and the type system is powerful enough, pasting a different, weaker, much less ergonomic programming language on top of your programming language is a bad way of implementing code generation.
- **A functional programming framework**. Mutation is not always bad and it’s sometimes unavoidable, but a functional *framework* makes everything more tidy. (Also, it’s much easier to implement a demo language if it’s functional. Sorry!😬) (Also note: this is not in Ket's scope but I believe a functional language can absolutely match imperative performance via by memory reusing, a concept that right now, for example, is being implemented in the [Roc](https://www.roc-lang.org/) language. That's a very good idea and it's great that it's been implemented! Roc looks like a really great project in many ways)

# Things that Ket is NOT:
- **a Programming language**: a CAP system is Much more general than that, and the idea that one has to learn a new syntax every time some guy wants to introduce some new innovation in programming, is Not the best we can do. How do you make this not happen: with a *flexible enough parser*, that can understand different flavour of syntax to express the same exact programming concepts that everybody uses. More of this later.
- **a Graphical programming environment**. Idk why one would want to get rid of text, text is great. (NOTE: *AS an input device for coding.* this DOESN’T mean that saving code in .txt files makes any sense. The project that is  doing the best hob with this is Unicode—)



# Features:
## incremental parsing + incremental typing
TODO

<!-- ## powerful code generation capabilities (can be made even more powerful):

T1 = [tloc1, tloc1->tloc2]
T2 = tloc2
Get*code(T1, T2):

(^ ok but we Dont have this??
Does rhis require th proving?)

## theorem proving:
[code generation and automatic reasoning/theorem proving are the same thing](http://nlab-pages.s3.us-east-2.amazonaws.com/nlab/show/propositions+as+types). Ket's theorem prover is at a very early demo stage.

Still, in [this video](https://www.youtube.com/watch?v=OLxbIXwpMes&ab_channel=MicrosoftResearch), estemed professor Timothy Gowers basically claims that proving such simple group theory theorem as "ab=ac implies b=c" is already a nice milestone for a theorem prover. Now, of course all existing theorem provers can prove this very easily. Still, I used it as a benchmark, and Ket can prove this theorem.

Of course, making a theorem prover truly useful and production ready requires still many advancements in AI, but this is absolutely necessary.

## personalized syntax
(Add sum syntax or smthg)

##  [Demo of integrating GPT code generation]:
what’s the idea here: just as a demo, we can hack the best AI we have at our disposal to already preview some decent code generation capabilities.
By using Ket's powerful type inference module, we can quickly present gpt3 with much better snippets than you’d do by hand. Also the returned code is tested.



- even if this is a demo, ket righ now can do most of the things Julia can do.
That’s because of Julia’s powerful type system, code generation, and reflection capabilities.
Join(heh, “f”)

- sql spitting
- It would be great to have a demo where moving .to_client. around changes produced code…

- a powerful default language
Again: ket is not a programming language. It’s more like a platform to builds programming languages on.
But, given the powerful (as in flexible) parser it features, the temptation to build what i think is a great syntax for a _productive_ language is very strong. See section below. -->


# Features Ket DOESN’T have but may have in the future/ ROADMAP:
 - **A much stronger theorem prover:** in particular, using AI as an heuristic for theorem proving tree search
 -  **Execution Cost semantics:** Mathematical treatment of type theory equates functions that produce the same behaviour, even if they have different runtime characteristics. Computational Type Theorists (CTT) have long been talking about aType Theory where this is baked in, but this doesnt exist in any software that I know of. Ket doesn’t currently have this at all. But, it’s an absolutely essential feature to allow powerful code generation

-  **Some form of dependent types:** Even if they are really popular in type theory, full dependendent types might not be that great of an idea. Anyway, Ket doesnt have them at all, yet

 - **memory reusing:** An execution optimization engine with memory reusing to avoid FP slowness, again see [Roc](https://www.roc-lang.org/).
 - **Heuristic parsing:** Incremental, interactive parsing is Good, but it Might get slow when there are thousands of syntactic rules around. Really, it's not even obvious that it will, but let's say it will. I’m fully convinced that a bit of (even very approximated) Bayesian statistics is a good enough heuristic to make the parser’s search routine usable and scalable.
- **Integrations with other languages/libraries**: Hooks to let Ket talk to and from at least some of the major programming languages. This is an enormous task, completely impossible to complete, and nobody can do it alone. Yet, every piece added to it increases Ket's usefulness as a real world programming framework.



# FAQ/ obvious criticisms:
## Waait… This is all cool, but aren’t deep language models able to turn natural language into code now, hence making the entire idea of coding obsolete?
Well *yes, yes they do*, ok?
Tell me about it!!\
Somehow, believe it or not, I started working on this entire project *before* that happened….\
I also started using Openai Codex the very day i got access to it after they released it.. And trust me, I’m never going to not use it again.

So where does that leave this project?

Well, consider this: remember that, even when deep language models (or more likely, some new iteration of the architecture) will be able to perform basic reasoning, we will always have a need for solid automatic reasoning engines.

I am completely sure our program verification/code generation tools/theorem provers/ whatever/ will get *more* powerful, not less, and we need strong reasoning engines to power them.

Even if we can achieve human-comparable levels of logical intelligence purely emergent from a huge ass deep model, we don’t want human- comparable, or even better-than-human logical intelligence from our: we want them to be -Just correct-…

But actually, there’s more: not only I think language models and theorem provers are incompatible. I actually think they will work together in the future!
In fact, language models are a very powerful heuristic for a theorem prover that performs proof search.

The idea here is of course inspired by Alphazero, which uses the big semantic-understanding models to Guide a good-old brute-force tree search, and at the same time trains the semantic understanding via reinforcement learning on the tree search data.\
That’s a beautiful, obviously powerful architecture, and I’m sure this will power our theorem provers for the foreseeable future!

The tree search in this case being the program verification/code generation tool/theorem prover/ whatever/ search, of course.
<!-- [[Of course(even if this has nothing to do with this project), if we get to the bottom of a truly right categorically-theory way to express reasoning via code, i feel like that will be the best starting point to build a neural architecture that natively supports this modality by having it hardwired internally.. Basically studying more math is always good is all I’m saying.]] -->


## Sooo this is implemented in Julia? You are telling me that you think that the secret for productivity is a statically typed, functional language, and you implement your compiler for it (?!?) in a dynamically typed imperative language? How does this make any sense? Are you completely stupid? Are you making fun of me???
Ok so there a few reasons for this.

I started with C++, I’m still seriously considering rust because 1. proper sum types and 2. Wasm.

But for now, I’m happy with julia, for these reasons:
- syntax. Julia syntax is mostly great, and in a crazy world where to buy a set of computational features, you have to buy the whole syntax, this Matters, of course. I Like being able to write—.
- The repl experience. Nothing to say, prototyping is Much faster. I want ket to be always eagerly executed and reactive, so even the repl experience will look bad in comparison, but you can’t do that today except in the Pluto notebooks, which is a pretty bad developer experience tho, or (i know) in some of those old and arcane Lispy things, that are even more useless.
- about Julia not being functional: I actually Don’t think mutability is bad, especially until a functional model will be optimized enough to make it useless. (Again, see Roc) In particolar, although Ket’s Typechecker code is mostly functional, Ket makes heavy use of mutability and references in the Parser code. So Ket won’t be actually implemented in a functional language any time soon, I’m afraid.
- Good code style: After all, Julia spits out LLVM code. Unfortunately i think it’s mostly impossible to use it *as* llvm code, ie without the julia runtime, but it’d be great if it was possible. It’s Often well typed, and it’s even Often functional (in case you don’t know julia, by convention all functions whose name don’t end in ! are pure).
- Powerful code generation and reflection capabilities. This allows even a demo like Ket to run at least Something.
- Related: the Codebase. Like, I won’t lie, Julia isnt even a bad language to target (as in, beyond the demo), because of how much great, useful code has been written in it now. By useful code i mean code that has real value: and by that i mean mostly mathematical code. When this whole decades long process of figuring out what our coding infrastructure is will end, we’ll find out that 99.9% of the code written around has no value. We Don’t need a thousand implementations of a web server. We Don’t need ginormous frameworks that only exist to glue together different frameworks ([like..](https://babeljs.io/))\
Here’s what we Do need, and has real value: *One* great differential equations package. *One* machine learning framework, written natively. *One* optimization package for each class of optimization problems. Etc. Julia is doing great with this.

Now, to prove that I’m Not 100% a julia fanboy: I think it’s a Disgrace that this (by now) huge amount of very useful code has been written in a language with Dynamic dispatch. \
Regardless of what Julia developers will tell you about practicality, Dynamic dispatch *is wrong*, unfortunalely. It’s wrong because it makes a mess of the distinction between subtyping and sum types, And it dumps this burden onto the runtime.\
The whole Ket philosophy is that *doing things right is better in the long run than doing them wrong*. And now we have all this great code in a wrong language.\
It’s practical, you say? Here’s what would be practical: if *entirely obvious compile time errors were signaled to me at compile time*, instead of hidden inside some huge run time call stack: *that* would be practical!


## Dont you think programming will never be easier? Who are you, to say coding is mostly accidental complexity? How long have you been coding? Don’t you know real world is messier than your nice mathematical abstractions? We have our legacy codebases to miantain, you know… Etc
So, the answer to the “Dont you think programming will never be easier?” question is: No, i don’t think that’s true. Despite what many programmers will tell you, [programming sucks](https://www.youtube.com/watch?v=MticYPfFRp8).

Luckily it sucks in a entirely preventable way, and so it *will* change. At the cost of dumping huge enough language models onto it that GPUs learn to do it instead of us.

It needs to be said that, even if many advancements have been made by thousands of great people throughout the decades, fixing programming once and for all unfortunately remains at the very bottom of *most* programmers’ priority list, for various reasons.\
Some reasons are legitimate, like, legacy codebases to miantain are a thing.\
And yet, at the cost of sounding brunt, I’ll also add that many of the reasons are rubbish, and to be clear, the programmers community at large is pretty luddist at this point.\
Multiple generations trained in very specific technologies and frameworks that happen to be completely arbitrary and bound to become obsolete in a matter of decades (if lucky) or years (more likely), cannot be good for anyone!\
*Exactly for this reason* we need a solid framework that removes accidental complexity, so it lasts for a while…

## Don’t you know X already exists/ there are even multiple versions around? Why are you reinventing X?
It can very well be the case that i don’t know. In that case, I’d be very grateful if you could send me to it!

But, to be honest, I’ve done quite a bit of research. See the following section to see a list of things i do know exist.

One last thing i want to add: if you are annoyed that I’m trying to “reinvent” tool X, ask yourself: Is tool X widely used by the programming community to make coding easier, or is it a niche tool? If it is the second, why?

*This* (creating a framework to make coding easier) is my goal, not developing some nice abstract algorithm.
Really, i don’t want to reinvent the wheel at all.

If nothing else, the fact that many tools that should be easily accessible, composable, and embeddable (e.g. in the theorem proving space) are instead written in obscure languages, locked behind arcane interfaces, and basically inaccessible without an ad-hoc university-level course, **IS** the problem here. The fact that they exist does very little to solve *this* problem.


<!-- -why the name, ket?
well, other than being the name of a beloved mathematical notation: my name (I’m the main developer of this) is Mike Tasca, Tasca being an italian surname that literally means Pocket. So it’s the last 3 letters of my surname.
If in a few years the backend of this will be built over the Roc language (which is entirely plausible), then the combined thing will have to be called Rocket. See what i did there? There’s only one letter change from my surname! -->




# Ketlang
Again: Ket is not a programming language. It’s more like a platform to build programming languages on.
But, given the powerful (as in flexible) parser it features, it's already relatively quick  to encode a default, example syntax for a what I think is a nice, simple functional language. (sorry, the temptation was too strong! I'm a software engineer, after all)

This syntax, which i’ll call KetLang, joins several very common ideas with a few powerful new ones. Here’s how it works:
- there are 3 different kinds of blocks you can write, and these are marked by the kind of parenthesis:
    - array/lists of homogeneous  types with `[]`
    - tuples/product types with `()` (but I’m seriously considering `<>`, since `()` is also syntax grouping And function application)
    - function bodies are `{}`. This is very common.

- The name of var can be specified as `{x—> x^2}`. This supports matching of sum types, with the `{a:A—>”its an A”, b:B—> “its a B”}` syntax, and will support unpacking, like `{(a:A, (b, c:C)—> c}`.
Furthermore, in cases where there is no ambiguity, `x` is the default name of the arg. This allows one to just write eg `{x^2}` for the square function, which is very very convenient. This exists in such beloved languages like APL and is clearly a great idea.

 - You can ofc call functions via `f(x)`. Also by name: `f(x=expr)`.

 - The core syntactic choice of KetLang is to favour function composition/piping. This is why the piping operator is the simplest one possible: `.` .
Although this can seem weird, it’s not so weird for the following reasons:
    - oop methods. In some oop heavy frameworks, people are already used to chaining methods, example.
    - properties/ fields. Even is non super heavily oop langs, you always access properies of structures via circle. Radius. In proper functional framework, radius is a _projection function_ that you chain to circle! So it makes perfect sense.

 - Contrary to almost all mainstream functional languages, in Ketlang (and in the whole Ket system, as a matter of fact), the normal form of functions is Uncurried. That is, they always take a product of multiple arguments and return a value, not a single arg and return another lambda. In my opinion, the Curried style is one of the main obstacles to a wider adoption of functional style, because that’s just not how people think.

In the Ket internals, this is taken even further: everything that is used inside a function is one of its parameters. So closure- like syntax like `a=3; {x+a}` is not a native ket program.
I actually consider this one of Ket’s best features, allowing for its nice modularity and incrementality.
But, ketlang supports this syntax ofc.

 - To make that syntax work, and also to make the most out of a piping syntax, partial application is crucial of course: this is because you want to write a data transformation like a tidy single chain of operations (along which, say, your object is mostly type stable), but every transformation wants secondary arg/ parameters/etc. the tidy way to write it is via partial application.\
Now, of course traditional functional, fully curried languages natively support partial application. *Except they dont*, because they expect args in * a given order*, and so it’s super annoying to partially apply say the second argument. Which is an entirely normal thing that one wants to do. This is their fundamental mistake.
KetLang supports partial application via the non very common syntax `f<scale=2>`. The use of `<>` instead of `()` means you are Refining the function, instead of fully executing it. You can find some familiarity with the c++ Templates syntax, even if this is Not the same thing of course.


        data . normalize . subtract<n=2> . print

 - Lastly. While `.` is basic piping, KetLang supports adding different syntaxes for Higher Order functions.\
Here's what this means. The most common Higher Order Function is Map. To square each element of a vector, this would be `my_vector .map<{x^2}>` (which already wouldn't be that bad), but instead of that, you can use the Enhanced Piping syntax `.|`. This becomes simply

        my_vector .|{x^2}

    This makes ketlang in a powerful array processing language. (By the way, thanks to proper handling of composition, map is just a different version of composition)\
    Another example is filtering. That would be `data .filter<{x<5}>`, but you can just write `data .f{x<5}`.  This makes for a powerful query language.
    (Now, this example doesn’t exactly work in this demo yet, for 2(related) reasons: the full arithmetic operations need to be implemented, and Full dependent typing is needed to properly type this. )

<!-- Also .?, and why its s but hard cuz theres Lots of exception around, which ones are implicit?. Maybe Roc is right again? -->

- As in most functional languages, including Roc, you can create local scopes for temporary variables with the `in` keyword. e.g., `(a=3+5 in a*a)` computes to 49 and `a` doesnt exist anymore outside that expression.
<!--
NOTE: Even with the syntax building features of Ket, building a completely new style of syntax requires a bit of work ofc. Here’s what Doesnt require any work: changing the specific delimiters in KetLang! You want to use |, or |> instead of . For piping? Or (why not) <..> for tuples? This is Literaly one line of code. That’s very very convenient! -->








# References/ list of things i Know exist:

http://www.lucacardelli.name/Papers/TypefulProg.pdf

TODO