SUBMISSION VERSION
==================

This is the BFS literal-wise version of the C^2 sentences generator which was originally used to generate sentences and 
plots for the original submission to IJCAI'23. Since the Frebruary of 2023 this version (0.x.y) is no longer supported 
as the clause-wise approach scales much faster (and was used for the final plots of the paper). 


SIMPLE USAGE
============

In order to run the sentence generator, you have to have installed Java (>=17). Then, it is as easy as 

```
 java -jar SFinder.jar
```

which runs the sentence generator with some predefined parameters, ultimately returning
```
# starting search with setup:	0.25.21	SentenceSetup{maxLayers=1000000000, maxClauses=3, maxLiteralsPerClause=4, predicates=[U0/1; B0/2], variables=[x; y], statesStoring=false, quantifiers=true, identityFilter=true, prover9Path=null, symmetryFlip=true, cellGraphPath=null, debug=false, cliffhangerFilter=true, juliaThreads=1, connectedComponents=true, naiveTautology=true, tautologyFilter=true, contradictionFilter=true, thetaReducibility=true, maxK=1, maxCountingClauses=1, maxLiteralsPerCountingClause=1, doubleCountingExist=false, maxProver9Seconds=30, languageBias=true, isoSings=true, isoPredicateNames=true, timeLimit=null}
# prover9 is  not used, the provided path does not exist
# cell graph script is  not used, the provided path does not exist
# starting layer 0 with 1 candidates	
(V x E y B0(x, y))
(E x U0(x))
(E x V y B0(x, y))
(E x E y B0(x, y))
(V x E=1 y B0(x, y))
(E=1 x U0(x))
(E=1 x V y B0(x, y))
# ending 0 with 11 candidates	 7 (0)
# starting layer 1 with 11 candidates	 7 (0)
```

-- where the first line lists all the setup
-- the second line says if prover9 was used
-- the third line says if cell-graph isomorphism was used
-- fourth line starts with `# starting layer X with Y candidates` expressing that the search started to evaluate sentences
of length `X` and with `Y` non-redundant candidates 
-- the line above is repeated (e.g. the last line) when a level is completed or started with information on the number of
reported non-redundant sentence and the time needed ([s] in brackets) to generate a particular layer
-- each other line contains exactly one non-redundant FO2/C2 sentence from corresponding layer of the search

The second and third lines are checks that you provided correct paths in order to use `Contradictions & Tautologies` and
`Cell Graph Isomorphis` respectively.


INSTALLATION
============

In order to use all pruning tricks, you have to install Prover9 and Julia.


CONTRADICTIONS & TAUTOLOGIES
----------------------------

You have to install Prover9 ( https://www.cs.unm.edu/~mccune/prover9/ ) on your machine, e.g. to download sources and 
build them or to use terminal on Linux with `sudo apt-get install -y prover9` command. 

Once you have installed Prover9, you may test that it works, e.g. typing in this folder

`/home/path-to-my-installation/LADR-2009-11A/bin/prover9 -f ./prover9examples/contradiction.in` 

and you should get the output stored in `./prover9examples/contradiction.out`

In order to use this in the sentence generator, you need the absolute path, let's say `path/prover9`, and add it to the
java call, e.g.

```
 java -Dida.sentenceSetup.prover9Path=path/prover9 -Dida.sentenceSetup.maxProver9Seconds=30 -jar SFinder.jar
```

where the latter of the two new parameters sets the time limit [s] on Prover9's execution per sentence (this is the 
default value). You can check that the generator got the correct path to Prover9 using the second line of the output.


CELL GRAPH ISOMORPHISM
-----------------------

In order to use this pruning technique, firstly you have to install Julia ( https://julialang.org/downloads/ >=1.8.2 ).
Then you have to compile Julia codes in `fwfomc` folder, so open terminal in this folder and type

```
julia --project=.\fwfomc -e "using Pkg; Pkg.instantiate();"
```

Further, type the following to test if the Julia project is running correctly
```
 julia --project=.\fwfomc .\fwfomc\scripts\compute_spectra.jl .\fwfomc\scripts\sample_input.in 7
```
you should obtain something like
```
(V x E y B0(x, y));1, 9, 343, 50625, 28629151, 62523502209, 532875860165503
(E x U0(x));1, 3, 7, 15, 31, 63, 127
(E x V y B0(x, y));1, 7, 169, 14911, 4925281, 6195974527, 30074093255809
(E x E y B0(x, y));1, 15, 511, 65535, 33554431, 68719476735, 562949953421311
(V x E=1 y B0(x, y));1, 4, 27, 256, 3125, 46656, 823543
(E=1 x U0(x));1, 2, 3, 4, 5, 6, 7
(E=1 x V y B0(x, y));1, 6, 147, 13500, 4617605, 5954619258, 29371110402823
```
If you don't see these line, then you most likely missed paths. One more test, type
```
julia --project=.\fwfomc .\fwfomc\scripts\compute_cell_graphs.jl .\fwfomc\scripts\sample_input.in
```
Again, you should obtain 
```
(V x E y B0(x, y));[W(1),L(n1, 1, -1), L(n2, 4, 1), L(n3, 4, 1), E(n1, n2, 2), E(n1, n3, 2), E(n2, n3, 4)]
(E x U0(x));[W(1), L(n1, 1, 1), L(n2, 1, 1), E(n1, n2, 1); W(-1), L(n1, 1, 1)]
(E x V y B0(x, y));[W(1), L(n1, 4, 1), L(n2, 4, 1), E(n1, n2, 4); W(-1), L(n1, 1, -1), L(n2, 4, 1), L(n3, 4, 1), E(n1, n2, 2), E(n1, n3, 2), E(n2, n3, 4)]
(E x E y B0(x, y));[W(1), L(n1, 4, 1), L(n2, 4, 1), E(n1, n2, 4); W(-1), L(n1, 1, 1)]
(V x E=1 y B0(x, y));[W(1),L(n1, 'x1^2 + 2*x1 + 1', 'x1'), L(n2, 'x1^2 + 2*x1 + 1', 1), L(n3, 1, -1), E(n1, n2, 'x1^2 + 2*x1 + 1'), E(n1, n3, 'x1 + 1'), E(n2, n3, 'x1 + 1')]
(E=1 x U0(x));[W(1),L(n1, 1, 'x1'), L(n2, 1, 1), E(n1, n2, 1)]
(E=1 x V y B0(x, y));[W(1),L(n1, 1, -1), L(n2, 4, 1), L(n3, 1, 'x1'), L(n4, 4, 1), E(n1, n2, 2), E(n1, n3, 1), E(n1, n4, 2), E(n2, n3, 2), E(n2, n4, 4), E(n3, n4, 2)]
```

Now, you have complied working the Julia part which is responsible for generating cell graphs for the sentence generator.
In order to use it in the generator, provide path `.\fwfomc\snippets\sample_multithreaded_unskolemized.jl` to it.

```
java -Dida.sentenceSetup.cellGraph=.\fwfomc\snippets\sample_multithreaded_unskolemized.jl -Dida.sentenceSetup.juliaThreads=10 -jar SFinder.jar
```

Again, you can verify that the generator found the path by inspecting the third line of the output. The latter parameter
sets the number of thread for Julia.


PARAMETERS OF THE GENERATOR
===========================

There is a bunch of parameters that can be played with in the generator. For start, you know how to employ the 
`Contradictions & Tautologies` and `CELL GRAPH ISOMORPHISM` pruning techniques. We will firstly cover language bias and
then go to explaining how to turn on the rest of the pruning techniques. It is done using `-Dproperty.name` which is 
either set to `true` (on) or `false` (off). These parameters are mostly independent of each other (yet some combination
of them does not have to make sense).

LANGUAGE BIAS
-------------

See the following command which runs a generator that generates FO2 sentences with at most 7 literals in total, at most 
six clauses, at most five literals per clause, four unary predicates and three binary predicates
```
 java
    -Dida.sentenceSetup.maxLayers=7
    -Dida.sentenceSetup.maxClauses=6
    -Dida.sentenceSetup.maxLiteralsPerClause=5
    -Dida.sentenceSetup.unaryPredicates=4
    -Dida.sentenceSetup.binaryPredicates=3
    -jar SFinder.jar
```

As of C2, the language bias is dependent on the following arguments
```
 java
    -Dida.sentenceSetup.maxK=3
    -Dida.sentenceSetup.maxLiteralsPerCountingClause=2 
    -Dida.sentenceSetup.maxCountingClauses=1
    -Dida.sentenceSetup.doubleCountingExist=false
    -jar ./out/artefact/SFinder_jar/SFinder.jar
```
where the generator would produce C2 sentence such with at most `E^{=3} x`, at most two literals per clause with a counting
quantifier, at most one clause with counting quantifier within a sentence, and forbidding `E^{=2} x E y` quantifiers (as
described in the appendix).


ISOMORPHIC SENTENCES
--------------------
```
 java
    -Dida.sentenceSetup.isoPredicateNames=true
    -jar SFinder.jar
```

DECOMPOSABLE SENTENCES
----------------------
```
 java
    -Dida.sentenceSetup.connectedComponents=true
    -jar SFinder.jar
```


NEGATIONS
---------
```
 java
    -Dida.sentenceSetup.isoSings=true
    -jar SFinder.jar
```


PERMUTING ARGUMENTS
-------------------
```
 java
    -Dida.sentenceSetup.symmetryFlip=true
    -jar SFinder.jar
```

TRIVIAL CONSTRAINTS
-------------------
```
 java
    -Dida.sentenceSetup.identityFilter=true
    -jar SFinder.jar
```


REFLEXIVE ATOMS
---------------
```
 java
    -Dida.sentenceSetup.cliffhangerFilter=true
    -jar SFinder.jar
```

SUBSUMPTION
-----------
```
 java
    -Dida.sentenceSetup.thetaReducibility=true
    -jar SFinder.jar
```

TIME LIMIT
----------
In case you're running out of time, set the time limit in minutes and the generator will end up as soon as possible after 
the limit
```
 java
    -Dida.sentenceSetup.timeLimit=60
    -jar ./out/artefact/SFinder_jar/SFinder.jar
```

Happy mining!


EXPERIMENTS SETUPS
==================

The experiments from the main paper corresponds to these generators calls with `cellPath/sample_multithreaded_unskolemized.jl` 
set to the Julia script and `proverPath/prover9` set Prover9 executable. 

for FO2
```
java -Xms5g -Xmx50g -Dida.sentenceSetup.timeLimit=2880 -Dida.sentenceSetup.maxLayers=10 -Dida.sentenceSetup.maxClauses=2 -Dida.sentenceSetup.maxLiteralsPerClause=5 -Dida.sentenceSetup.unaryPredicates=1 -Dida.sentenceSetup.binaryPredicates=1 -Dida.sentenceSetup.quantifiers=true -Dida.sentenceSetup.maxK=0 -Dida.sentenceSetup.maxCountingClauses=2 -Dida.sentenceSetup.maxLiteralsPerCountingClause=1 -Dida.sentenceSetup.doubleCountingExist=false -Dida.sentenceSetup.lexicographicalComparatorOnly=false -Dida.sentenceSetup.languageBias=true -Dida.sentenceSetup.prover9Path=none -Dida.sentenceSetup.maxProver9Seconds=30 -Dida.sentenceSetup.naiveTautology=false -Dida.sentenceSetup.tautologyFilter=false -Dida.sentenceSetup.contradictionFilter=false -Dida.sentenceSetup.countingContradictionFilter=false -Dida.sentenceSetup.connectedComponents=true -Dida.sentenceSetup.isoPredicateNames=false -Dida.sentenceSetup.isoSings=false -Dida.sentenceSetup.symmetryFlip=false -Dida.sentenceSetup.identityFilter=false -Dida.sentenceSetup.thetaReducibility=false  -Dida.sentenceSetup.cliffhangerFilter=false -Dida.sentenceSetup.cellGraph=none -Dida.sentenceSetup.storeStates=false  -jar SFinder.jar 
java -Xms5g -Xmx50g -Dida.sentenceSetup.timeLimit=2880 -Dida.sentenceSetup.maxLayers=10 -Dida.sentenceSetup.maxClauses=2 -Dida.sentenceSetup.maxLiteralsPerClause=5 -Dida.sentenceSetup.unaryPredicates=1 -Dida.sentenceSetup.binaryPredicates=1 -Dida.sentenceSetup.quantifiers=true -Dida.sentenceSetup.maxK=0 -Dida.sentenceSetup.maxCountingClauses=2 -Dida.sentenceSetup.maxLiteralsPerCountingClause=1 -Dida.sentenceSetup.doubleCountingExist=false -Dida.sentenceSetup.lexicographicalComparatorOnly=false -Dida.sentenceSetup.languageBias=true -Dida.sentenceSetup.prover9Path=proverPath/prover9 -Dida.sentenceSetup.maxProver9Seconds=30 -Dida.sentenceSetup.naiveTautology=true -Dida.sentenceSetup.tautologyFilter=true -Dida.sentenceSetup.contradictionFilter=true -Dida.sentenceSetup.countingContradictionFilter=true -Dida.sentenceSetup.connectedComponents=true -Dida.sentenceSetup.isoPredicateNames=true -Dida.sentenceSetup.isoSings=false -Dida.sentenceSetup.symmetryFlip=false -Dida.sentenceSetup.identityFilter=false -Dida.sentenceSetup.thetaReducibility=false  -Dida.sentenceSetup.cliffhangerFilter=false -Dida.sentenceSetup.cellGraph=none -Dida.sentenceSetup.storeStates=false  -jar SFinder.jar
java -Xms5g -Xmx50g -Dida.sentenceSetup.timeLimit=2880 -Dida.sentenceSetup.maxLayers=10 -Dida.sentenceSetup.maxClauses=2 -Dida.sentenceSetup.maxLiteralsPerClause=5 -Dida.sentenceSetup.unaryPredicates=1 -Dida.sentenceSetup.binaryPredicates=1 -Dida.sentenceSetup.quantifiers=true -Dida.sentenceSetup.maxK=0 -Dida.sentenceSetup.maxCountingClauses=2 -Dida.sentenceSetup.maxLiteralsPerCountingClause=1 -Dida.sentenceSetup.doubleCountingExist=false -Dida.sentenceSetup.lexicographicalComparatorOnly=false -Dida.sentenceSetup.languageBias=true -Dida.sentenceSetup.prover9Path=proverPath/prover9 -Dida.sentenceSetup.maxProver9Seconds=30 -Dida.sentenceSetup.naiveTautology=true -Dida.sentenceSetup.tautologyFilter=true -Dida.sentenceSetup.contradictionFilter=true -Dida.sentenceSetup.countingContradictionFilter=true -Dida.sentenceSetup.connectedComponents=true -Dida.sentenceSetup.isoPredicateNames=true -Dida.sentenceSetup.isoSings=true -Dida.sentenceSetup.symmetryFlip=false -Dida.sentenceSetup.identityFilter=false -Dida.sentenceSetup.thetaReducibility=false  -Dida.sentenceSetup.cliffhangerFilter=false -Dida.sentenceSetup.cellGraph=none -Dida.sentenceSetup.storeStates=false  -jar SFinder.jar
java -Xms5g -Xmx50g -Dida.sentenceSetup.timeLimit=2880 -Dida.sentenceSetup.maxLayers=10 -Dida.sentenceSetup.maxClauses=2 -Dida.sentenceSetup.maxLiteralsPerClause=5 -Dida.sentenceSetup.unaryPredicates=1 -Dida.sentenceSetup.binaryPredicates=1 -Dida.sentenceSetup.quantifiers=true -Dida.sentenceSetup.maxK=0 -Dida.sentenceSetup.maxCountingClauses=2 -Dida.sentenceSetup.maxLiteralsPerCountingClause=1 -Dida.sentenceSetup.doubleCountingExist=false -Dida.sentenceSetup.lexicographicalComparatorOnly=false -Dida.sentenceSetup.languageBias=true -Dida.sentenceSetup.prover9Path=proverPath/prover9 -Dida.sentenceSetup.maxProver9Seconds=30 -Dida.sentenceSetup.naiveTautology=true -Dida.sentenceSetup.tautologyFilter=true -Dida.sentenceSetup.contradictionFilter=true -Dida.sentenceSetup.countingContradictionFilter=true -Dida.sentenceSetup.connectedComponents=true -Dida.sentenceSetup.isoPredicateNames=true -Dida.sentenceSetup.isoSings=true -Dida.sentenceSetup.symmetryFlip=true -Dida.sentenceSetup.identityFilter=false -Dida.sentenceSetup.thetaReducibility=false  -Dida.sentenceSetup.cliffhangerFilter=false -Dida.sentenceSetup.cellGraph=none -Dida.sentenceSetup.storeStates=false -jar SFinder.jar
java -Xms5g -Xmx50g -Dida.sentenceSetup.timeLimit=2880 -Dida.sentenceSetup.maxLayers=10 -Dida.sentenceSetup.maxClauses=2 -Dida.sentenceSetup.maxLiteralsPerClause=5 -Dida.sentenceSetup.unaryPredicates=1 -Dida.sentenceSetup.binaryPredicates=1 -Dida.sentenceSetup.quantifiers=true -Dida.sentenceSetup.maxK=0 -Dida.sentenceSetup.maxCountingClauses=2 -Dida.sentenceSetup.maxLiteralsPerCountingClause=1 -Dida.sentenceSetup.doubleCountingExist=false -Dida.sentenceSetup.lexicographicalComparatorOnly=false -Dida.sentenceSetup.languageBias=true -Dida.sentenceSetup.prover9Path=proverPath/prover9 -Dida.sentenceSetup.maxProver9Seconds=30 -Dida.sentenceSetup.naiveTautology=true -Dida.sentenceSetup.tautologyFilter=true -Dida.sentenceSetup.contradictionFilter=true -Dida.sentenceSetup.countingContradictionFilter=true -Dida.sentenceSetup.connectedComponents=true -Dida.sentenceSetup.isoPredicateNames=true -Dida.sentenceSetup.isoSings=true -Dida.sentenceSetup.symmetryFlip=true -Dida.sentenceSetup.identityFilter=true -Dida.sentenceSetup.thetaReducibility=true  -Dida.sentenceSetup.cliffhangerFilter=true -Dida.sentenceSetup.cellGraph=none -Dida.sentenceSetup.storeStates=false  -jar SFinder.jar
java -Xms5g -Xmx50g -Dida.sentenceSetup.timeLimit=2880 -Dida.sentenceSetup.maxLayers=10 -Dida.sentenceSetup.maxClauses=2 -Dida.sentenceSetup.maxLiteralsPerClause=5 -Dida.sentenceSetup.unaryPredicates=1 -Dida.sentenceSetup.binaryPredicates=1 -Dida.sentenceSetup.quantifiers=true -Dida.sentenceSetup.maxK=0 -Dida.sentenceSetup.maxCountingClauses=2 -Dida.sentenceSetup.maxLiteralsPerCountingClause=1 -Dida.sentenceSetup.doubleCountingExist=false -Dida.sentenceSetup.lexicographicalComparatorOnly=false -Dida.sentenceSetup.languageBias=true -Dida.sentenceSetup.prover9Path=proverPath/prover9 -Dida.sentenceSetup.maxProver9Seconds=30 -Dida.sentenceSetup.naiveTautology=true -Dida.sentenceSetup.tautologyFilter=true -Dida.sentenceSetup.contradictionFilter=true -Dida.sentenceSetup.countingContradictionFilter=true -Dida.sentenceSetup.connectedComponents=true -Dida.sentenceSetup.isoPredicateNames=true -Dida.sentenceSetup.isoSings=true -Dida.sentenceSetup.symmetryFlip=true -Dida.sentenceSetup.identityFilter=true -Dida.sentenceSetup.thetaReducibility=true  -Dida.sentenceSetup.cliffhangerFilter=true -Dida.sentenceSetup.cellGraph=cellPath/sample_multithreaded_unskolemized.jl -Dida.sentenceSetup.storeStates=false -Dida.sentenceSetup.juliaThreads=30 -jar SFinder.jar
```

and in the same fashion for C2
```
java -Xms5g -Xmx50g -Dida.sentenceSetup.timeLimit=2880 -Dida.sentenceSetup.maxLayers=10 -Dida.sentenceSetup.maxClauses=2 -Dida.sentenceSetup.maxLiteralsPerClause=5 -Dida.sentenceSetup.unaryPredicates=1 -Dida.sentenceSetup.binaryPredicates=1 -Dida.sentenceSetup.quantifiers=true -Dida.sentenceSetup.maxK=1 -Dida.sentenceSetup.maxCountingClauses=2 -Dida.sentenceSetup.maxLiteralsPerCountingClause=1 -Dida.sentenceSetup.doubleCountingExist=false -Dida.sentenceSetup.lexicographicalComparatorOnly=false -Dida.sentenceSetup.languageBias=true -Dida.sentenceSetup.prover9Path=none -Dida.sentenceSetup.maxProver9Seconds=30 -Dida.sentenceSetup.naiveTautology=false -Dida.sentenceSetup.tautologyFilter=false -Dida.sentenceSetup.contradictionFilter=false -Dida.sentenceSetup.countingContradictionFilter=false -Dida.sentenceSetup.connectedComponents=true -Dida.sentenceSetup.isoPredicateNames=false -Dida.sentenceSetup.isoSings=false -Dida.sentenceSetup.symmetryFlip=false -Dida.sentenceSetup.identityFilter=false -Dida.sentenceSetup.thetaReducibility=false  -Dida.sentenceSetup.cliffhangerFilter=false -Dida.sentenceSetup.cellGraph=none -Dida.sentenceSetup.storeStates=false  -jar SFinder.jar 
java -Xms5g -Xmx50g -Dida.sentenceSetup.timeLimit=2880 -Dida.sentenceSetup.maxLayers=10 -Dida.sentenceSetup.maxClauses=2 -Dida.sentenceSetup.maxLiteralsPerClause=5 -Dida.sentenceSetup.unaryPredicates=1 -Dida.sentenceSetup.binaryPredicates=1 -Dida.sentenceSetup.quantifiers=true -Dida.sentenceSetup.maxK=1 -Dida.sentenceSetup.maxCountingClauses=2 -Dida.sentenceSetup.maxLiteralsPerCountingClause=1 -Dida.sentenceSetup.doubleCountingExist=false -Dida.sentenceSetup.lexicographicalComparatorOnly=false -Dida.sentenceSetup.languageBias=true -Dida.sentenceSetup.prover9Path=proverPath/prover9 -Dida.sentenceSetup.maxProver9Seconds=30 -Dida.sentenceSetup.naiveTautology=true -Dida.sentenceSetup.tautologyFilter=true -Dida.sentenceSetup.contradictionFilter=true -Dida.sentenceSetup.countingContradictionFilter=true -Dida.sentenceSetup.connectedComponents=true -Dida.sentenceSetup.isoPredicateNames=true -Dida.sentenceSetup.isoSings=false -Dida.sentenceSetup.symmetryFlip=false -Dida.sentenceSetup.identityFilter=false -Dida.sentenceSetup.thetaReducibility=false  -Dida.sentenceSetup.cliffhangerFilter=false -Dida.sentenceSetup.cellGraph=none -Dida.sentenceSetup.storeStates=false  -jar SFinder.jar
java -Xms5g -Xmx50g -Dida.sentenceSetup.timeLimit=2880 -Dida.sentenceSetup.maxLayers=10 -Dida.sentenceSetup.maxClauses=2 -Dida.sentenceSetup.maxLiteralsPerClause=5 -Dida.sentenceSetup.unaryPredicates=1 -Dida.sentenceSetup.binaryPredicates=1 -Dida.sentenceSetup.quantifiers=true -Dida.sentenceSetup.maxK=1 -Dida.sentenceSetup.maxCountingClauses=2 -Dida.sentenceSetup.maxLiteralsPerCountingClause=1 -Dida.sentenceSetup.doubleCountingExist=false -Dida.sentenceSetup.lexicographicalComparatorOnly=false -Dida.sentenceSetup.languageBias=true -Dida.sentenceSetup.prover9Path=proverPath/prover9 -Dida.sentenceSetup.maxProver9Seconds=30 -Dida.sentenceSetup.naiveTautology=true -Dida.sentenceSetup.tautologyFilter=true -Dida.sentenceSetup.contradictionFilter=true -Dida.sentenceSetup.countingContradictionFilter=true -Dida.sentenceSetup.connectedComponents=true -Dida.sentenceSetup.isoPredicateNames=true -Dida.sentenceSetup.isoSings=true -Dida.sentenceSetup.symmetryFlip=false -Dida.sentenceSetup.identityFilter=false -Dida.sentenceSetup.thetaReducibility=false  -Dida.sentenceSetup.cliffhangerFilter=false -Dida.sentenceSetup.cellGraph=none -Dida.sentenceSetup.storeStates=false  -jar SFinder.jar
java -Xms5g -Xmx50g -Dida.sentenceSetup.timeLimit=2880 -Dida.sentenceSetup.maxLayers=10 -Dida.sentenceSetup.maxClauses=2 -Dida.sentenceSetup.maxLiteralsPerClause=5 -Dida.sentenceSetup.unaryPredicates=1 -Dida.sentenceSetup.binaryPredicates=1 -Dida.sentenceSetup.quantifiers=true -Dida.sentenceSetup.maxK=1 -Dida.sentenceSetup.maxCountingClauses=2 -Dida.sentenceSetup.maxLiteralsPerCountingClause=1 -Dida.sentenceSetup.doubleCountingExist=false -Dida.sentenceSetup.lexicographicalComparatorOnly=false -Dida.sentenceSetup.languageBias=true -Dida.sentenceSetup.prover9Path=proverPath/prover9 -Dida.sentenceSetup.maxProver9Seconds=30 -Dida.sentenceSetup.naiveTautology=true -Dida.sentenceSetup.tautologyFilter=true -Dida.sentenceSetup.contradictionFilter=true -Dida.sentenceSetup.countingContradictionFilter=true -Dida.sentenceSetup.connectedComponents=true -Dida.sentenceSetup.isoPredicateNames=true -Dida.sentenceSetup.isoSings=true -Dida.sentenceSetup.symmetryFlip=true -Dida.sentenceSetup.identityFilter=false -Dida.sentenceSetup.thetaReducibility=false  -Dida.sentenceSetup.cliffhangerFilter=false -Dida.sentenceSetup.cellGraph=none -Dida.sentenceSetup.storeStates=false -jar SFinder.jar
java -Xms5g -Xmx50g -Dida.sentenceSetup.timeLimit=2880 -Dida.sentenceSetup.maxLayers=10 -Dida.sentenceSetup.maxClauses=2 -Dida.sentenceSetup.maxLiteralsPerClause=5 -Dida.sentenceSetup.unaryPredicates=1 -Dida.sentenceSetup.binaryPredicates=1 -Dida.sentenceSetup.quantifiers=true -Dida.sentenceSetup.maxK=1 -Dida.sentenceSetup.maxCountingClauses=2 -Dida.sentenceSetup.maxLiteralsPerCountingClause=1 -Dida.sentenceSetup.doubleCountingExist=false -Dida.sentenceSetup.lexicographicalComparatorOnly=false -Dida.sentenceSetup.languageBias=true -Dida.sentenceSetup.prover9Path=proverPath/prover9 -Dida.sentenceSetup.maxProver9Seconds=30 -Dida.sentenceSetup.naiveTautology=true -Dida.sentenceSetup.tautologyFilter=true -Dida.sentenceSetup.contradictionFilter=true -Dida.sentenceSetup.countingContradictionFilter=true -Dida.sentenceSetup.connectedComponents=true -Dida.sentenceSetup.isoPredicateNames=true -Dida.sentenceSetup.isoSings=true -Dida.sentenceSetup.symmetryFlip=true -Dida.sentenceSetup.identityFilter=true -Dida.sentenceSetup.thetaReducibility=true  -Dida.sentenceSetup.cliffhangerFilter=true -Dida.sentenceSetup.cellGraph=none -Dida.sentenceSetup.storeStates=false  -jar SFinder.jar
java -Xms5g -Xmx50g -Dida.sentenceSetup.timeLimit=2880 -Dida.sentenceSetup.maxLayers=10 -Dida.sentenceSetup.maxClauses=2 -Dida.sentenceSetup.maxLiteralsPerClause=5 -Dida.sentenceSetup.unaryPredicates=1 -Dida.sentenceSetup.binaryPredicates=1 -Dida.sentenceSetup.quantifiers=true -Dida.sentenceSetup.maxK=1 -Dida.sentenceSetup.maxCountingClauses=2 -Dida.sentenceSetup.maxLiteralsPerCountingClause=1 -Dida.sentenceSetup.doubleCountingExist=false -Dida.sentenceSetup.lexicographicalComparatorOnly=false -Dida.sentenceSetup.languageBias=true -Dida.sentenceSetup.prover9Path=proverPath/prover9 -Dida.sentenceSetup.maxProver9Seconds=30 -Dida.sentenceSetup.naiveTautology=true -Dida.sentenceSetup.tautologyFilter=true -Dida.sentenceSetup.contradictionFilter=true -Dida.sentenceSetup.countingContradictionFilter=true -Dida.sentenceSetup.connectedComponents=true -Dida.sentenceSetup.isoPredicateNames=true -Dida.sentenceSetup.isoSings=true -Dida.sentenceSetup.symmetryFlip=true -Dida.sentenceSetup.identityFilter=true -Dida.sentenceSetup.thetaReducibility=true  -Dida.sentenceSetup.cliffhangerFilter=true -Dida.sentenceSetup.cellGraph=cellPath/sample_multithreaded_unskolemized.jl -Dida.sentenceSetup.storeStates=false -Dida.sentenceSetup.juliaThreads=30 -jar SFinder.jar
```


SPECTRA COMPUTATION
=====================

If you want to compute combinatorial spectra for an output of the generator with `N` elements, execute the following command
(which you actually used during the installation where `N = 7`)

```
 julia --project=.\fwfomc .\fwfomc\scripts\compute_spectra.jl .\path\to\generator.stdout N
```

You will obtain lines of the form `sentence ; combinatorial_spectrum`.


