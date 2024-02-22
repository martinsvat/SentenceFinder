This repository contains C2 sentence generator -- a part of a bigger machine learning approach that aims to  generate  
`interesting` combinator integer sequences that can be encoded using a subset of first-order logic. The original work was
published in the paper`On Discovering Interesting Combinatorial Integer Sequences` IJCAI'23 (extended appendix available
at `https://arxiv.org/abs/2302.04606`) and subsequently extended in `Relaxing Deductive and Inductive Reasoning in 
Relational Logic` (dissertation). A snapshot of the database from the original paper is available at `https://fluffy.jung.ninja` 
-- indeed, you can have `.ninja` as a TLD! Some of our generated sequences made it to the OEIS -- behold 
`https://oeis.org/search?q=arxiv%3A2302.04606&sort=&language=english&go=Search`.


# Land of the sentence miners welcomes you

Dear wanderer!

Welcome in the land of sentences where you can FO2 and C2 sentences. To mine FO2 sentences with at most 5 clauses,
4 literals per clause, 3 unary and 2 binary predicates, run the following command

```
 java
    -Dida.sentenceSetup.maxClauses=5
    -Dida.sentenceSetup.maxLiteralsPerClause=4
    -Dida.sentenceSetup.unaryPredicates=3
    -Dida.sentenceSetup.binaryPredicates=2
    -Dida.sentenceSetup.quantifiers=true
    -Dida.sentenceSetup.maxOverallLiterals=-1
    -jar ./out/artefact/SFinder_jar/SFinder.jar
```

In the end, you will eventually mine a sentence that has at most 20 literals in total. If you'd like to mine shorter
sentences, e.g. 10 literals, set `maxOverallLiterals=10` instead of `-1` which is equivalent
of `maxClauses * maxLiteralsPerClause`.

To allow forall and exists quantifiers set `quantifiers=true`, otherwise only forall quantifiers are allowed.

To mine C2 sentences, e.g. `k` being at most 1, at most 2 clauses with a counting quantifier, and at most 3 literals
per counting clause, use the following command

```
 java
    -Dida.sentenceSetup.maxK=1
    -Dida.sentenceSetup.maxCountingClauses=2
    -Dida.sentenceSetup.maxLiteralsPerCountingClause=3
    -Dida.sentenceSetup.doubleCountingExist=true
    -jar ./out/artefact/SFinder_jar/SFinder.jar
```

To forbid computationally expensive spectra of some clauses, set `doubleCountingExist=false` which
forbids `E x E^{=k} y`,
`E^{=k} x E y`, and `E^{=k} x E^{=l} y` quantifiers.

Pruning techniques
------------------

Since the early days of the BFS version spanning the space in literal-wise manner, version 0.x.y described in 
`On Discovering Interesting Combinatorial Integer Sequences` IJCAI'23, we have come a long path to the current version
1.x.y, which works in clause-wise manner. The basic stones of this version are clauses, which are firstly generated, 
and then only those non-redundant (e.g. non-theta-reducible) are connected via `&` to generate sentences. Therefore,
some techniques described in the original paper are no longer `not-safe-to-delete` but `safe-to-delete` instead.

```
 java
    -Dida.sentenceSetup.languageBias=true
    -Dida.sentenceSetup.decomposableComponents=true
    -Dida.sentenceSetup.isomorphicSentences=true
    -Dida.sentenceSetup.negations=true
    -Dida.sentenceSetup.permutingArguments=true
    -Dida.sentenceSetup.subsumption=true
    -Dida.sentenceSetup.trivialConstraints=true
    -Dida.sentenceSetup.quantifiersReducibility=true
    -jar ./out/artefact/SFinder_jar/SFinder.jar
```

When `subsumption=true` all theta-reducible clauses are thrown out. Trivial constraints are in clause-wise approach
safe-to-delete. `quantifiersReducibility=true` extends Subsumption from the original paper beyond to different 
combinations of quantifiers (it's called `\theta*` in the second paper).

There is `lexicographicalMatching` which, when set to `true`, switches the underlying engine to do pruning based on 
lexicographically minimal version of sentence (isomorphic setences, negations, and permuting arguments have to be turned
on). It is more memory efficient than using the subsumption engine for this task. `languageBias=true` allows only 
refinements which are "lexicographically minimal"; e.g. having `V x U0(x)`, then `V x U0(x) | U1(x)` is allowed while
`V x U0(x) | U2(x)` isn't.

Proving related pruning techniques
----------------------------------

```
 java
    -Dida.sentenceSetup.naiveTautology=true
    -Dida.sentenceSetup.tautologyFilter=true
    -Dida.sentenceSetup.contradictionFilter=true
    -Dida.sentenceSetup.prover9Path=path/to/prover9/executable
    -Dida.sentenceSetup.maxProver9Seconds=30
    -jar ./out/artefact/SFinder_jar/SFinder.jar
```

The most efficient way to get rid of naive tautologies is to use `naiveTautology=true` which forbids all formulas
such that `E/V x R(x) v ~R(x)`. This is much faster than to invoke Prover9 each time. 

In order to use either `tautologyFilter` or `contradictionFilter` you have to set path to Prover9 executable using
`prover9Path` (if that fails, you'll find out from the output). Finally, use `maxProver9Seconds` to limit the execution
time of Prover9.


Hiding related techniques
--------------------------

```
 java
    -Dida.sentenceSetup.reflexiveAtoms=true
    -jar ./out/artefact/SFinder_jar/SFinder.jar
```

Cell Graph Isomorphism
----------------------

```
 java
    -Dida.sentenceSetup.cellGraph=path/to/sample_multithreaded_unskolemized
    -Dida.sentenceSetup.juliaThreads=10
    -Dida.sentenceSetup.cellTimeLimit=3600
    -Dida.sentenceSetup.redis=redis://mypass@127.0.0.1:6379/0
    -Dida.sentenceSetup.canonicalCellGraphs=false
    -jar ./out/artefact/SFinder_jar/SFinder.jar
```

Cell graphs construction is quite costly operation, so if you're going to call SFinder quite often, it might be quite
good thing to cache them. To do this, everything you need to turn on Redis and insert connection URI using `redis`. You
need to execute the `java` command from a folder where you have installed the FastWFOMC project (see the installation 
section).

The cell time limit is experimental yet and does not work correctly right now. Actually, the time limit is forwarded 
to Julia package that computes cell graphs; however, the implementation of the time limit is yet to be done. Implementing 
this time limit in Java was much slower due to Julia's package invocation and hence did not make it into a stable version.  
Canonical computation of cell graphs, i.e., `canonicalCellGraphs`, is another experimental setup which is left for future
development since it boils down to computing canonical representation of a complete weighted graph which is infeasible 
with the current prototypical backend that lacks any advanced way to handle that problem; hence the `false` value implies 
usage of hypergraph isomorphism based on SAT.

Finally, note that the current implementation does not handle cell graphs dependent on both `n` and `k`, i.e., 
`V x E^{=k} y phi(x,y)`. Bear this in mind and run SFinder without cell graph pruning when allowing `k >= 1`.


Miscellaneous
-------------

```
 java
    -Xms15g
    -Xmx50g
    -Djava.util.concurrent.ForkJoinPool.common.parallelism=10
    -Dida.sentenceSetup.debug=false
    -Dida.sentenceSetup.timeLimit=3600
    -Dida.sentenceSetup.seed="(V x U0(x))"
    -Dida.sentenceSetup.statesStoring=true
    -jar ./out/artefact/SFinder_jar/SFinder.jar
    > sentences.txt
    2> storedSearchStates.txt
```

If you are too weak, literally running out of manna on every breath, just increase it, e.g. it using `-Xms` & `-Xmx`.
If you are running too late, increase the pool of threads using `java.util.concurrent.ForkJoinPool.common.parallelism`,
because SFinder now supports parallelism as well. The `debug` is turned off right now, but may be used in the future.
There are few clock gates, i.e. lines of codes, in each of them the current run-time is compared to `timeLimit` [s] and
the execution is stopped if the time limit is reached.

If you wanna start to mine clauses with non-empty sentence, you may put a formula into the `seed`. The sentence
in `seed` is fixed (no clause can be refined) and the output will still be lexicographically minimal (w.r.t. predicates
given at the start); the number of literals are excluded from the limits of, `maxLiteralsPerClause`. However, 
`maxCountingClauses`, and `maxClauses` still apply the final sentences. Bear in mind that all other filters apply for 
the final clauses, e.g. trivial constraints. Predicates used in the seeds have to be in form of `Ux/1` and `Bx/2`
starting from 0 to at most n-ary literals. Otherwise, the search won't start. Layers correspond to the number of literals
in a sentence excluding those in the seed (contrary seed's clauses are included in `maxClauses`).

Here, a `seed` is a FO2/C2 sentence. There are few constraints on the sentences:
-- they must look as an output of this precious mining tool (CNF)
-- first variable must be named `x` and the second must be named `y`
-- the first variable must be used in the sentence (e.g. `V x E y U(y)` fails)
-- the number of predicates must be within the range of limits (parameters)

By using `statesStoring=true`, SFinder spams stderr with auxiliary data which it can use in the future to continue in the
search from the previous point it ended. Once you'd like to continue with mining, just put second file as the value of
`loadErrOut`, e.g.

```
    java
        -Dida.sentenceSetup.loadErrOut=storedSearchStates.txt
        -jar ./out/artefact/SFinder_jar/SFinder.jar
        > sentences.txt
        2> storedSearchStates2.txt
```

Output
------

There are two possible types of line on the output: i) comment ii) a sentence. A comment line starts with `#`, e.g.

```
# theta-reduction done within 0 resulting in 337 with distribution 1:32, 2:102, 3:203
# going to connect clauses with connection filters: DisjunctiveClauses, ConnectedComponents, QuantifiersReducibility, TrivialConstraints
```

A sentence line contains a sentence which is in lexicographically minimal form given predicates' names, negation signs,
direction of binary predicates, e.g.

```
(E x B0(x, x)) & (V x E=1 y ~B0(x, y))
(E x E y B0(x, x) | ~B0(x, y))
```

The algorithm outputs sentences as soon as possible. Hence, in case of BFS, cell graph pruning is done after each layer.

DFS
---

Up till now, the search was driven in breadth-first fashion using clauses as basic building blocks. However, you may 
switch to depth-first strategy using
```
    java
        -Dida.sentenceSetup.mode=dfs
        -jar ./out/artefact/SFinder_jar/SFinder.jar
```

This will change the search strategy, the usage of pruning or hiding techniques (e.g. reflexive atoms will be a pruning 
technique instead of a hiding one), and the output, which will be in the form 

```
(E x B0(x, x)) & (E=1 x V y ~B0(x, y)) & (V x E=1 y ~B0(x, y))	
(E x B0(x, x)) & (E=1 x V y ~B0(x, y)) & (V x E=1 y ~B0(y, x))	
# opened 10 (10 / 10 / 18) [157] in 150	(E x B0(x, x)) & (E=1 x V y ~B0(x, y))
```

Where the last comment line reports currently opened node (with some search statistics), and is preceded by newly generated
sentences that have not been seen so far. DFS mode does not support load-&-continue mode.

As of now, the DFS mode is a way slower and rather experimental. 


INSTALLATION
============

Install Java 16 or higher. Install Redis (https://redis.io/docs/getting-started/installation/) if you want to use it for
caching cell graphs. You may use the fat jar `SFinder.jar` or build your own using the codes (with all the required 
libraris in `dependencies`).

Prover9
-------

Filtering out contradictions relies on Prover9 installed on your system (
see `https://www.cs.unm.edu/~mccune/prover9/manual/2009-11A/`,
`https://www.cs.unm.edu/~mccune/prover9/`), e.g. to download sources and build them or to use terminal on Linux with
`sudo apt-get install -y prover9` command. Once you have installed Prover9, you may test that it works, e.g. typing in
this folder

```
/home/path-to-my-installation/LADR-2009-11A/bin/prover9 -f ./prover9examples/contradiction.in
```

and you should get the output stored in `./prover9examples/contradiction.out`

Finally, when you want to use Prover9 inside your mining-like day, provide the path to the Prover9's executable:

```
 java
    -Dida.sentenceSetup.prover9Path=/home/path-to-my-installation/LADR-2009-11A/bin/prover9
    -Dida.sentenceSetup.maxProver9Seconds=30
    -Dida.sentenceSetup.tautologyFilter=true
    -Dida.sentenceSetup.contradictionFilter=true
    -jar ./out/artefact/SFinder_jar/SFinder.jar
```

If the executable was find, you will be noticed that both filters are used, e.g.

```
# starting to generate clauses with filters: MaxLiterals:3, MaxLiteralsPerCountingClause:1, NaiveTautologyFilter, TautologyFilter30
# going to connect clauses with sentence filters: ContradictionFilter30
```

otherwise you'll end up with

```
# starting to generate clauses with filters: TFwithNonexistingPath
# going to connect clauses with sentence filters: CFwithNonexistingPath
```

This implementation was developed using `Prover9 (32) version Dec-2007, Dec 2007.` To test that your version of Prover9
works as expected, check `prover9expamples` folder with inputs and outputs. Similarly, it should be easy to extend the
filter to work with E, Mace4, and others provers. The `maxProver9Seconds` sets the time limit [s] prover9 can run.


Cell graph isomorphism
----------------------

For non-trivial same-sequence sentences, there is a cell-graph filter which can hide them, but it is costly. It also
looks for inter-level isomorphisms. First, install Julia (https://julialang.org/downloads/ >=1.8.2). Second, download
FastWFOMC

```
 git clone https://github.com/jan-toth/FastWFOMC.jl.git
```

compile Julia codes in the downloaded repo, i.e.

```
 julia --project=.\FastWFOMC.jl -e "using Pkg; Pkg.instantiate();"
```

Finally, to plug it into your mining tool, set `cellGraph` to the following .jl script 

```
 cd FastWFOMC.jl
 java
    -Dida.sentenceSetup.cellGraph=.\julia\sample_multithreaded_unskolemized.jl
    -Dida.sentenceSetup.juliaThreads=10
    -Dida.sentenceSetup.cellTimeLimit=3600
    -jar ../out/artefact/SFinder_jar/SFinder.jar
```

The cell time limit is not working as of this version.

In case the script file is not found by the mining tool, you won't see this in the first setup line:

```
# starting search with setup:	x.y.z	SentenceSetup{...,cellGraphPath=.\julia\sample_multithreaded_unskolemized.jl,...}
```

but `null` value instead. The important thing is to run the `java` command from the folder you have installed FastWFOMC.
Otherwise, you might run into problem of not being able to execute that cell graph computation from within java.


FAREWELL
========

If it happens that you reached the end of the mining, you will obtain

```
# the search has ended!
```

in the output. However, you can sharpen your pickaxe and continue with yet another mining!

Happy mining!

This mining operation is only possibly thanks to the work of Ondrej Kuzelka (`Matching`), work behind Sat4J, Prover9,
FastWFOMC, and Redis.


Versions
========

You should be mining instead of reading this page. However, below you can see the development the mining tool which gets
cooler with every single step of development
(`layer: visible sentences (after pruning, raw generated) in time [raw generation, pruning, hiding, printing]`).

```
# info: 1: 8 (12, 32) in 0 [ 0, 0, 0, 0]; 2: 89 (109, 458) in 10 [ 0, 10, 0, 0]; 3: 845 (1014, 6353) in 167 [ 0, 166, 1, 0]; # starting search with setup:	1.0.0	SentenceSetup{maxOverallLiterals=9, maxClauses=3, maxLiteralsPerClause=3, predicates=[U0/1; B0/2], variables=[x; y], statesStoring=true, quantifiers=true, reflexiveAtoms=true, prover9Path=D:\Program Files (x86)\Prover9-Mace4\bin-win32\prover9.exe, errOut=null, permutingArguments=true, cellGraphPath=C:\data\school\development\sequence-db\fluffy-broccoli\SFinder\julia\sample_multithreaded_unskolemized.jl, debug=false, trivialConstraints=true, juliaThreads=10, decomposableComponents=true, naiveTautology=true, tautologyFilter=true, contradictionFilter=true, subsumption=true, quantifiersReducibility=true, maxK=1, maxCountingClauses=1, maxLiteralsPerCountingClause=1, doubleCountingExist=false, countingContradictionFilter=false, maxProver9Seconds=30, seed=, negations=true, isomorphicSentences=true, timeLimit=null, cellTimeLimit=3600, redis=redis://mypass@127.0.0.1:6379/, forkPollSize=10}
# info: 1: 8 (12, 32) in 0 [ 0, 0, 0, 0]; 2: 86 (100, 259) in 5  [ 0, 5, 0, 0];  3: 769 (878, 2869) in 73 [ 0, 72, 1, 0];    # starting search with setup:	1.0.1	SentenceSetup{maxOverallLiterals=9, maxClauses=3, maxLiteralsPerClause=3, predicates=[U0/1; B0/2], variables=[x; y], statesStoring=true, quantifiers=true, reflexiveAtoms=true, prover9Path=D:\Program Files (x86)\Prover9-Mace4\bin-win32\prover9.exe, errOut=null, permutingArguments=true, cellGraphPath=C:\data\school\development\sequence-db\fluffy-broccoli\SFinder\julia\sample_multithreaded_unskolemized.jl, debug=false, trivialConstraints=true, juliaThreads=10, decomposableComponents=true, naiveTautology=true, tautologyFilter=true, contradictionFilter=true, subsumption=true, quantifiersReducibility=true, maxK=1, maxCountingClauses=1, maxLiteralsPerCountingClause=1, doubleCountingExist=false, countingContradictionFilter=false, maxProver9Seconds=30, seed=, negations=true, isomorphicSentences=true, timeLimit=null, cellTimeLimit=3600, redis=redis://mypass@127.0.0.1:6379/, forkPollSize=10} 
# info: 1: 8 (12, 32) in 0 [ 0, 0, 0, 0]; 2: 87 (101, 281) in 15 [ 0, 5, 10, 0]; 3: 789 (898, 3170) in 90 [ 0, 72, 18, 0];   # starting search with setup:	1.0.2	SentenceSetup{maxOverallLiterals=9, maxClauses=3, maxLiteralsPerClause=3, predicates=[U0/1; B0/2], variables=[x; y], statesStoring=false, quantifiers=true, reflexiveAtoms=true, prover9Path=D:\Program Files (x86)\Prover9-Mace4\bin-win32\prover9.exe, errOut=null, permutingArguments=true, cellGraphPath=C:\data\school\development\sequence-db\fluffy-broccoli\SFinder\julia\sample_multithreaded_unskolemized.jl, debug=false, trivialConstraints=true, juliaThreads=10, decomposableComponents=true, naiveTautology=true, tautologyFilter=true, contradictionFilter=true, subsumption=true, quantifiersReducibility=true, maxK=1, maxCountingClauses=1, maxLiteralsPerCountingClause=1, doubleCountingExist=false, countingContradictionFilter=false, maxProver9Seconds=30, seed=, negations=true, isomorphicSentences=true, timeLimit=null, cellTimeLimit=3600, redis=redis://mypass@127.0.0.1:6379/, forkPollSize=10}
# info: 1: 8 (12, 32) in 0 [ 0, 0, 0, 0]; 2: 87 (101, 281) in 5  [ 0, 5, 0, 0];  3: 789 (898, 3170) in 79 [ 0, 78, 1, 0];    # starting search with setup:	1.1.2	SentenceSetup{maxOverallLiterals=9, maxClauses=3, maxLiteralsPerClause=3, predicates=[U0/1; B0/2], variables=[x; y], statesStoring=false, quantifiers=true, reflexiveAtoms=true, prover9Path=D:\Program Files (x86)\Prover9-Mace4\bin-win32\prover9.exe, errOut=null, permutingArguments=true, cellGraphPath=C:\data\school\development\sequence-db\fluffy-broccoli\SFinder\julia\sample_multithreaded_unskolemized.jl, debug=false, trivialConstraints=true, juliaThreads=10, decomposableComponents=true, naiveTautology=true, tautologyFilter=true, contradictionFilter=true, subsumption=true, quantifiersReducibility=true, maxK=1, maxCountingClauses=1, maxLiteralsPerCountingClause=1, doubleCountingExist=false, countingContradictionFilter=false, maxProver9Seconds=30, seed=, negations=true, isomorphicSentences=true, timeLimit=null, cellTimeLimit=3600, redis=redis://mypass@127.0.0.1:6379/, forkPollSize=10}
# info: 1: 8 (12, 32) in 0 [ 0, 0, 0, 0]; 2: 84 (96, 269) in 6 [ 0, 6, 0, 0];    3: 685 (780, 2756) in 76 [ 0, 75, 1, 0];    # starting search with setup:	1.2.2	SentenceSetup{maxOverallLiterals=9, maxClauses=3, maxLiteralsPerClause=3, predicates=[U0/1; B0/2], variables=[x; y], statesStoring=false, quantifiers=true, reflexiveAtoms=true, prover9Path=D:\Program Files (x86)\Prover9-Mace4\bin-win32\prover9.exe, errOut=null, permutingArguments=true, cellGraphPath=C:\data\school\development\sequence-db\fluffy-broccoli\SFinder\julia\sample_multithreaded_unskolemized.jl, debug=false, trivialConstraints=true, juliaThreads=10, decomposableComponents=true, naiveTautology=true, tautologyFilter=true, contradictionFilter=true, subsumption=true, quantifiersReducibility=true, maxK=1, maxCountingClauses=1, maxLiteralsPerCountingClause=1, doubleCountingExist=false, countingContradictionFilter=false, maxProver9Seconds=30, seed=, negations=true, isomorphicSentences=true, timeLimit=null, cellTimeLimit=3600, redis=redis://mypass@127.0.0.1:6379/, forkPollSize=10}

# info: 1: 12 (12, 32) in 0 [ 0, 0, 0, 0]; 2: 86 (96, 269) in 6 [ 0, 6, 0, 0]; 3: 725 (780, 2756) in 72 [ 0, 72, 0, 0];     # starting search with setup:	1.2.2i	SentenceSetup{maxOverallLiterals=9, maxClauses=3, maxLiteralsPerClause=3, predicates=[U0/1; B0/2], variables=[x; y], statesStoring=false, quantifiers=true, reflexiveAtoms=true, prover9Path=D:\Program Files (x86)\Prover9-Mace4\bin-win32\prover9.exe, errOut=null, permutingArguments=false, cellGraphPath=null, debug=false, trivialConstraints=true, juliaThreads=10, decomposableComponents=true, naiveTautology=true, tautologyFilter=true, contradictionFilter=true, subsumption=true, quantifiersReducibility=true, maxK=1, maxCountingClauses=1, maxLiteralsPerCountingClause=1, doubleCountingExist=false, countingContradictionFilter=false, maxProver9Seconds=30, seed=, negations=false, isomorphicSentences=false, timeLimit=null, cellTimeLimit=3600, redis=redis://mypass@127.0.0.1:6379/, forkPollSize=10}
# info: 1: 12 (12, 32) in 0 [ 0, 0, 0, 0]; 2: 86 (96, 269) in 6 [ 0, 6, 0, 0]; 3: 725 (780, 2756) in 73 [ 0, 73, 0, 0];     # starting search with setup:	1.2.2i	SentenceSetup{maxOverallLiterals=9, maxClauses=3, maxLiteralsPerClause=3, predicates=[U0/1; B0/2], variables=[x; y], statesStoring=false, quantifiers=true, reflexiveAtoms=true, prover9Path=D:\Program Files (x86)\Prover9-Mace4\bin-win32\prover9.exe, errOut=null, permutingArguments=true, cellGraphPath=null, debug=false, trivialConstraints=true, juliaThreads=10, decomposableComponents=true, naiveTautology=true, tautologyFilter=true, contradictionFilter=true, subsumption=true, quantifiersReducibility=true, maxK=1, maxCountingClauses=1, maxLiteralsPerCountingClause=1, doubleCountingExist=false, countingContradictionFilter=false, maxProver9Seconds=30, seed=, negations=true, isomorphicSentences=true, timeLimit=null, cellTimeLimit=3600, redis=redis://mypass@127.0.0.1:6379/, forkPollSize=10}
# info: 1: 8  (12, 32) in 0 [ 0, 0, 0, 0]; 2: 84 (96, 269) in 6 [ 0, 6, 0, 0]; 3: 685 (780, 2756) in 79 [ 0, 78, 1, 0];     # starting search with setup:	1.2.2i	SentenceSetup{maxOverallLiterals=9, maxClauses=3, maxLiteralsPerClause=3, predicates=[U0/1; B0/2], variables=[x; y], statesStoring=false, quantifiers=true, reflexiveAtoms=true, prover9Path=D:\Program Files (x86)\Prover9-Mace4\bin-win32\prover9.exe, errOut=null, permutingArguments=true, cellGraphPath=C:\data\school\development\sequence-db\fluffy-broccoli\SFinder\julia\sample_multithreaded_unskolemized.jl, debug=false, trivialConstraints=true, juliaThreads=10, decomposableComponents=true, naiveTautology=true, tautologyFilter=true, contradictionFilter=true, subsumption=true, quantifiersReducibility=true, maxK=1, maxCountingClauses=1, maxLiteralsPerCountingClause=1, doubleCountingExist=false, countingContradictionFilter=false, maxProver9Seconds=30, seed=, negations=true, isomorphicSentences=true, timeLimit=null, cellTimeLimit=3600, redis=redis://mypass@127.0.0.1:6379/, forkPollSize=10}
# info: 1: 8  (12, 32) in 0 [ 0, 0, 0, 0]; 2: 84 (96, 269) in 7 [ 0, 7, 0, 0]; 3: 709 (803, 2835) in 100 [ 0, 98, 2, 0];    # starting search with setup:	1.2.3i	SentenceSetup{maxOverallLiterals=9, maxClauses=3, maxLiteralsPerClause=3, predicates=[U0/1; B0/2], variables=[x; y], statesStoring=false, quantifiers=true, reflexiveAtoms=true, prover9Path=D:\Program Files (x86)\Prover9-Mace4\bin-win32\prover9.exe, errOut=null, permutingArguments=true, cellGraphPath=C:\data\school\development\sequence-db\fluffy-broccoli\SFinder\julia\sample_multithreaded_unskolemized.jl, debug=false, trivialConstraints=true, juliaThreads=10, decomposableComponents=true, naiveTautology=true, tautologyFilter=true, contradictionFilter=true, subsumption=true, quantifiersReducibility=true, maxK=1, maxCountingClauses=1, maxLiteralsPerCountingClause=1, doubleCountingExist=false, countingContradictionFilter=false, maxProver9Seconds=30, seed=, negations=true, isomorphicSentences=true, timeLimit=null, cellTimeLimit=3600, redis=redis://mypass@127.0.0.1:6379/, forkPollSize=10}
# info: 1: 8  (12, 32) in 0 [ 0, 0, 0, 0]; 2: 84 (96, 269) in 6 [ 0, 6, 0, 0]; 3: 709 (803, 2835) in 83 [ 0, 81, 2, 0];     # starting search with setup:	1.3.3i	SentenceSetup{maxOverallLiterals=9, maxClauses=3, maxLiteralsPerClause=3, predicates=[U0/1; B0/2], variables=[x; y], statesStoring=false, quantifiers=true, reflexiveAtoms=true, prover9Path=D:\Program Files (x86)\Prover9-Mace4\bin-win32\prover9.exe, errOut=null, permutingArguments=true, cellGraphPath=C:\data\school\development\sequence-db\fluffy-broccoli\SFinder\julia\sample_multithreaded_unskolemized.jl, debug=false, trivialConstraints=true, juliaThreads=10, decomposableComponents=true, naiveTautology=true, tautologyFilter=true, contradictionFilter=true, subsumption=true, quantifiersReducibility=true, maxK=1, maxCountingClauses=1, maxLiteralsPerCountingClause=1, doubleCountingExist=false, countingContradictionFilter=false, maxProver9Seconds=30, seed=, negations=true, isomorphicSentences=true, timeLimit=null, cellTimeLimit=3600, redis=redis://mypass@127.0.0.1:6379/, forkPollSize=10, languageBias=true}

# info: 1: 11 (12, 32) in 30 [ 0, 0, 30, 0]; 2: 86 (96, 269) in 30 [ 0, 6, 24, 0]; 3: 708 (803, 2835) in 165 [ 0, 71, 94, 0];   # starting search with setup:	1.4.5	SentenceSetup{maxOverallLiterals=9, maxClauses=3, maxLiteralsPerClause=3, predicates=[U0/1; B0/2], variables=[x; y], statesStoring=false, quantifiers=true, reflexiveAtoms=true, prover9Path=D:\Program Files (x86)\Prover9-Mace4\bin-win32\prover9.exe, errOut=null, permutingArguments=true, cellGraph=C:\data\school\development\sequence-db\fluffy-broccoli\SFinder\julia\sample_multithreaded_unskolemized.jl, debug=false, trivialConstraints=true, juliaThreads=10, decomposableComponents=true, naiveTautology=true, tautologyFilter=true, contradictionFilter=true, subsumption=true, quantifiersReducibility=true, maxK=1, maxCountingClauses=1, maxLiteralsPerCountingClause=1, doubleCountingExist=false, countingContradictionFilter=false, maxProver9Seconds=30, seed=, negations=true, isomorphicSentences=true, timeLimit=null, cellTimeLimit=3600, redis=redis://mypass@127.0.0.1:6379/, forkPollSize=10, languageBias=true, lexicographicalMatching=true}
# info: 1: 11 (12, 32) in 20 [ 0, 0, 20, 0]; 2: 83 (96, 269) in 25 [ 0, 6, 19, 0]; 3: 644 (803, 2835) in 260 [ 0, 69, 191, 0];  # starting search with setup:	1.5.6d	0.1	SentenceSetup{maxOverallLiterals=3, maxClauses=3, maxLiteralsPerClause=3, predicates=[U0/1; B0/2], variables=[x; y], statesStoring=false, quantifiers=true, reflexiveAtoms=true, prover9Path=D:\Program Files (x86)\Prover9-Mace4\bin-win32\prover9.exe, errOut=null, permutingArguments=true, cellGraph=C:\data\school\development\sequence-db\fluffy-broccoli\SFinder\julia\sample_multithreaded_unskolemized.jl, debug=false, trivialConstraints=true, juliaThreads=10, decomposableComponents=true, naiveTautology=true, tautologyFilter=true, contradictionFilter=true, subsumption=true, quantifiersReducibility=true, maxK=1, maxCountingClauses=1, maxLiteralsPerCountingClause=1, doubleCountingExist=false, countingContradictionFilter=false, maxProver9Seconds=30, seed=, negations=true, isomorphicSentences=true, timeLimit=null, cellTimeLimit=3600, redis=redis://mypass@127.0.0.1:6379/, forkPollSize=10, languageBias=true, lexicographicalMatching=true, canonicalCellGraphs=true, fastWfOMCVersion=0.1, mode=bfs}
# info: 1: 11 (12, 32) in 27 [ 0, 1, 26, 0]; 2: 83 (96, 269) in 37 [ 0, 8, 29, 0]; 3: 644 (803, 2835) in 273 [ 0, 111, 162, 0]; # starting search with setup:	1.5.10	0.1	SentenceSetup{maxOverallLiterals=9, maxClauses=3, maxLiteralsPerClause=3, predicates=[U0/1; B0/2], variables=[x; y], statesStoring=true, quantifiers=true, reflexiveAtoms=true, prover9Path=D:\Program Files (x86)\Prover9-Mace4\bin-win32\prover9.exe, errOut=null, permutingArguments=true, cellGraph=C:\data\school\development\sequence-db\fluffy-broccoli\SFinder\julia\sample_multithreaded_unskolemized.jl, debug=false, trivialConstraints=true, juliaThreads=10, decomposableComponents=true, naiveTautology=true, tautologyFilter=true, contradictionFilter=true, subsumption=true, quantifiersReducibility=true, maxK=1, maxCountingClauses=1, maxLiteralsPerCountingClause=1, doubleCountingExist=false, countingContradictionFilter=false, maxProver9Seconds=30, seed=, negations=true, isomorphicSentences=true, timeLimit=null, cellTimeLimit=3600, redis=redis://mypass@127.0.0.1:6379/, forkPollSize=10, languageBias=true, lexicographicalMatching=true, canonicalCellGraphs=false, fastWfOMCVersion=0.1, mode=bfs}
```


Experiments
===========

See below a command that reproduces the FO2 experiment from the original paper with all pruning and hiding techniques
turned on (you have to add your path to prover9 and test the cell graph path).
```
java -Xms5g -Xmx50g -Dida.sentenceSetup.timeLimit=2880 -Dida.sentenceSetup.maxOverallLiterals=10 -Dida.sentenceSetup.maxClauses=2 -Dida.sentenceSetup.maxLiteralsPerClause=5 -Dida.sentenceSetup.unaryPredicates=1 -Dida.sentenceSetup.binaryPredicates=1 -Dida.sentenceSetup.quantifiers=true -Dida.sentenceSetup.maxK=0 -Dida.sentenceSetup.maxCountingClauses=2 -Dida.sentenceSetup.maxLiteralsPerCountingClause=1 -Dida.sentenceSetup.doubleCountingExist=false -Dida.sentenceSetup.languageBias=true -Dida.sentenceSetup.prover9Path=.../.../prover9 -Dida.sentenceSetup.maxProver9Seconds=30 -Dida.sentenceSetup.naiveTautology=true -Dida.sentenceSetup.tautologyFilter=true -Dida.sentenceSetup.contradictionFilter=true  -Dida.sentenceSetup.decomposableComponents=true -Dida.sentenceSetup.isomorphicSentences=true -Dida.sentenceSetup.negations=true -Dida.sentenceSetup.permutingArguments=true -Dida.sentenceSetup.reflexiveAtoms=true -Dida.sentenceSetup.subsumption=true  -Dida.sentenceSetup.trivialConstraints=true -Dida.sentenceSetup.quantifiersReducibility=true -Dida.sentenceSetup.cellGraph=./julia/sample_multithreaded_unskolemized.jl   -jar SFinder.jar
```

The rest of experiments can be easily obtained by altering this command; e.g. `maxK=1` to get C2 experiments, 
`trivialConstraints=false` to turn of trivial constraints feature, and so on. This will give a little smaller numbers as 
`quantifiersReducibility` was fixed and enhanced heavily from the version 0.x.y.

See the folder `experiments` that contains some experiments from the paper as well as a prototypical infrastructure to
run further experiments and aggregate their results.