import re
import os
from pathlib import Path

import pandas as pd
from models.db_utils import create_engine

import typing as t
import typer

# MAX_TIME = 60 * 60
MAX_TIME = 60 * 5


def loadFailedSpectra(csv: Path) -> t.Dict['sentence', float]:
    # data = pd.read_csv(csv, delimiter=";")
    result = {}
    if not csv.exists():
        return result
    #
    # for row in data.to_numpy():
    with open(csv, 'r') as file:
        for line in file.readlines():
            sentence = line.split(";")[1]
            if sentence in result:
                continue
            result[sentence] = MAX_TIME
    return result


def loadSpectraTimes(csv: Path) -> t.Tuple[t.Dict['sentence', float], t.Dict['sentence', str]]:
    if not csv.exists():
        return ({}, {})
    data = pd.read_csv(csv)
    timeResult = {}
    spectraResult = {}
    for sentence, times, sequence in data.to_numpy():
        if sentence in timeResult:
            continue
        spectrum = sequence.split(",")
        # if len(spectrum) < 10:
        #     continue
        trueTime = len(spectrum) == 400 or len(spectrum[-1]) >= 200
        # tady je chyba protoze MAX_TIME se nikdy nebere protoze ty nebudou v tabulce sentence
        time = sum(map(float, times.split(","))) if trueTime else MAX_TIME
        timeResult[sentence] = time
        spectraResult[sentence] = sequence

    # not nice!
    with open(Path(".", "martin_out.txt"), 'r') as file:
        for line in file.readlines():
            if len(line.strip()) < 1:
                continue
            msg, sentence, times, spectrum = line.split(";")
            if sentence in timeResult:
                continue
            spectrum = sequence.split(",")
            # if len(spectrum) < 10:
            #     continue
            trueTime = len(spectrum) == 400 or len(spectrum[-1]) >= 200
            # tady je chyba protoze MAX_TIME se nikdy nebere protoze ty nebudou v tabulce sentence
            time = sum(map(float, times.split(","))) if trueTime else MAX_TIME
            timeResult[sentence] = time
            spectraResult[sentence] = sequence

    return timeResult, spectraResult


def loadSpectraTimesFromFile(csv: Path) -> t.Tuple[t.Dict['sentence', float], t.Dict['sentence', str]]:
    if not csv.exists():
        return ({}, {})

    timeResult = {}
    spectraResult = {}
    with open(csv, 'r') as f:
        for line in f.readlines():
            if not line.strip().startswith("("):
                continue

            split = line.strip().split(";")
            sentence = split[0].strip()
            sequence = split[1].strip()
            times = split[2].strip()
            if sentence in timeResult:
                continue
            spectrum = sequence.split(",")
            # if len(spectrum) < 10:
            #     continue
            trueTime = len(spectrum) == 400 or len(spectrum[-1]) >= 200
            #  MAX_TIME se nikdy nebere protoze ty nebudou v tabulce sentence
            time = sum(map(float, times.split(","))) if trueTime else MAX_TIME
            timeResult[sentence] = time
            spectraResult[sentence] = sequence

    return timeResult, spectraResult


def areAllConsistent(grabbed: t.List[t.Dict[str, t.Any]]) -> bool:
    values = set()
    for data in grabbed:
        values.add("-".join(data[key] for key in ["timeLimit",
                                                  "maxOverallLiterals",
                                                  "maxClauses",
                                                  "maxLiteralsPerClause",
                                                  "predicates",
                                                  "variables",
                                                  "quantifiers",
                                                  "maxK",
                                                  "maxCountingClauses",
                                                  "maxLiteralsPerCountingClause",
                                                  "doubleCountingExist",
                                                  # "version"
                                                  ]))
    # for v in values:
    #     print(v)
    return 1 == len(values)


def dataToCumulativeCurve(values: t.List[t.Tuple[int, int]], division: int = 1, xShift: int = 0,
                          yInitAddition: int = 0) -> str:
    points = []
    if yInitAddition != 0:
        values[0] = (values[0][0], values[0][1] + yInitAddition)
    for x, y in values:
        if len(points) > 0:
            y = y + points[-1][1]
        points.append([x + xShift, y if y != 0 else division * 0.00001])
    return " ".join(f"({x}, {y if 1 == division else 1.0 * y / division:.3f})" for x, y in points)
    # return ", ".join(f"({key}, {val})" for key, val in values)


def incorporateStats(line: str, result: t.Dict[str, t.Any]) -> None:
    # # info: 1: 7 (8, 20) in 8 [ 0, 0, 8, 0]; 2: 40 (48, 143) in 9 [ 0, 0, 9, 0];
    #     #lits: vis (after pruning, raw) in total-layer-time [raw generation, pruning, filtering, printing out]
    if not line.startswith("# info:"):
        raise ValueError()
    line = line[len("# info:"):]

    if "time" not in result:
        result["time"] = {}
    if "candidates" not in result:
        result["candidates"] = {}

    for part in line.split(";"):
        if len(part.strip()) == 0:
            continue
        # 1: 7 (8, 20) in 8 [ 0, 0, 8, 0]
        part = part.replace("(", "").replace(")", "").replace(":", "").replace("in", "").replace("[", "") \
            .replace("]", "").replace(",", "")
        layerIdx, displayedSentences, afterPruningSentences, rawSentences, layerTime, rawGenerationTime, pruningTime, filteringTime, printingTime = [
            int(e) for e in part.split()]
        result["time"][layerIdx] = layerTime
        result["candidates"][layerIdx] = displayedSentences


def parseSetupLine(line) -> t.Dict[str, t.Any]:
    # e.g # starting search with setup:	0.24.19	SentenceSetup{maxLayers=6, maxClauses=3, maxLiteralsPerClause=2, predicates=[U0/1; U1/1; B0/2; B1/2], variables=[x; y], statesStoring=false, quantifiers=true, identityFilter=true, prover9Path=/usr/bin/prover9, errOut=null, symmetryFlip=true, cellGraphPath=null, debug=false, cliffhangerFilter=false, juliaThreads=10, connectedComponents=true, naiveTautology=true, tautologyFilter=true, contradictionFilter=true, thetaReducibility=true, quantifiersReducibility=false, maxK=1, maxCountingClauses=3, maxLiteralsPerCountingClause=1, doubleCountingExist=false, countingContradictionFilter=true, maxProver9Seconds=30, seed=, languageBias=true, isoSings=true, isoPredicateNames=true, lexicographicalComparatorOnly=false, timeLimit=10, fixedSeed=true}
    # # starting search with setup:	1.0.1	SentenceSetup{maxOverallLiterals=10, maxClauses=2, maxLiteralsPerClause=5, predicates=[U0/1; B0/2], variables=[x; y], statesStoring=false, quantifiers=true, reflexiveAtoms=true, prover9Path=/home/kuzelon2/LADR-2009-11A/bin/prover9, errOut=null, permutingArguments=true, cellGraphPath=/home/kuzelon2/cw-experiments/sample_multithreaded_unskolemized.jl, debug=false, trivialConstraints=true, juliaThreads=30, decomposableComponents=true, naiveTautology=true, tautologyFilter=true, contradictionFilter=true, subsumption=true, quantifiersReducibility=true, maxK=0, maxCountingClauses=2, maxLiteralsPerCountingClause=1, doubleCountingExist=false, countingContradictionFilter=false, maxProver9Seconds=30, seed=, negations=true, isomorphicSentences=true, timeLimit=2880, cellTimeLimit=3600, redis=redis://mypass@127.0.0.1:6379/, forkPollSize=10}

    result: t.Dict[str, t.Any] = {}
    line = line.split("setup:", 1)[1]
    version, line = line.split("SentenceSetup", 1)
    result["version"] = version.strip()

    line = line.strip()
    line = line[1:-1]

    pair = {'\'': '\'',
            '"': '"',
            '(': None,
            '{': None,
            '[': None,
            ')': '(',
            '}': '{',
            ']': '['
            }
    lastCut = 0
    stack = []
    for index in range(0, len(line)):
        element = line[index]
        if element in pair:
            startPoint = pair[element]
            if len(stack) == 0 or None is startPoint or stack[-1] != startPoint:
                stack.append(element)
            else:
                if stack[-1] == startPoint:
                    del stack[-1]
                else:
                    raise ValueError()

        if (element == "," and len(stack) == 0) or index == len(line) - 1:
            key, val = line[lastCut:index].split("=", 1)
            result[key.strip()] = val.strip()
            lastCut = index + 1

    return result


def firstNumberToInt(line: str) -> int:
    # # clauses generated within 62 overall 1027 with distribution 1:20, 2:133, 3:300, 4:362, 5:212
    # # theta-reduction done within 0 resulting in 404 with distribution 1:20, 2:81, 3:101, 4:116, 5:86
    for token in line.split():
        try:
            val = int(token)
            return val
        except Exception as e:
            continue
    return -1


def addTo(value: int, basket: t.Dict[str, t.Any], key: str, initIfMissing: int) -> None:
    if key not in basket:
        basket[key] = initIfMissing
    basket[key] += value


# TODO make this method nicer andr easier to read :))
def readFile(child: Path, sentenceTime: t.Dict['sentence', float], spectra: t.Dict['sentence', str] = None) -> t.Dict[
    str, t.Any]:
    if None is spectra:
        spectra = {}
    result: t.Dict[str, t.Any] = {}
    result["index"] = fetchIndex(str(child.name))

    # # starting search with setup:	1.0.1	SentenceSetup{maxOverallLiterals=10, maxClauses=2, maxLiteralsPerClause=5, predicates=[U0/1; B0/2], variables=[x; y], statesStoring=false, quantifiers=true, reflexiveAtoms=true, prover9Path=/home/kuzelon2/LADR-2009-11A/bin/prover9, errOut=null, permutingArguments=true, cellGraphPath=/home/kuzelon2/cw-experiments/sample_multithreaded_unskolemized.jl, debug=false, trivialConstraints=true, juliaThreads=30, decomposableComponents=true, naiveTautology=true, tautologyFilter=true, contradictionFilter=true, subsumption=true, quantifiersReducibility=true, maxK=0, maxCountingClauses=2, maxLiteralsPerCountingClause=1, doubleCountingExist=false, countingContradictionFilter=false, maxProver9Seconds=30, seed=, negations=true, isomorphicSentences=true, timeLimit=2880, cellTimeLimit=3600, redis=redis://mypass@127.0.0.1:6379/, forkPollSize=10}
    # clauses generation
    # # clauses generated within 62 overall 1027 with distribution 1:20, 2:133, 3:300, 4:362, 5:212
    # # theta-reduction done within 0 resulting in 404 with distribution 1:20, 2:81, 3:101, 4:116, 5:86
    # each layer ends with
    # # info: 1: 7 (8, 20) in 8 [ 0, 0, 8, 0]; 2: 40 (48, 143) in 9 [ 0, 0, 9, 0];
    #     #lits: vis (after pruning, raw) in total-layer-time [raw generation, pruning, filtering, printing out]

    clausesTimes = {}
    with open(child) as file:
        for line in file.readlines():
            if line.startswith("# starting search with setup:"):
                result.update(parseSetupLine(line))
            elif line.startswith("# clauses generated within") or line.startswith(
                    "# theta-reduction done within") or line.startswith("# quantifiers reducibility done within"):
                addTo(firstNumberToInt(line), result, "initTime", 0)
            elif line.startswith("# info:"):
                incorporateStats(line, result)
            elif line.startswith("("):
                clause = line.split(";")[0].strip()  # legacy code
                # layer = sum(map(len, [e for sub in clause.split("&") for e in sub.split("|")]))
                layer = len([e for sub in clause.split("&") for e in sub.split("|")])
                if layer not in clausesTimes:
                    clausesTimes[layer] = {"missed": 0, "hits": 0, "time": [], "spectra": []}
                if clause in sentenceTime:
                    clausesTimes[layer]["hits"] = clausesTimes[layer]["hits"] + 1
                    clausesTimes[layer]["time"].append(sentenceTime[clause])
                    if clause in spectra:
                        clausesTimes[layer]["spectra"].append(spectra[clause])
                else:
                    # correct version
                    clausesTimes[layer]["missed"] = clausesTimes[layer]["missed"] + 1
                    # pessimistic version
                    # clausesTimes[layer]["hits"] = clausesTimes[layer]["hits"] + 1
                    # clausesTimes[layer]["time"].append(MAX_TIME)


    maxLayer = len(result["time"])
    approxSequenceTime = []  # [(0, 0)]
    minSpectra = []  # (0, 1)
    uniquePrefixes = set()
    for layer in sorted(clausesTimes.keys()):
        if 0 == clausesTimes[layer]["hits"]:
            print(
                f"not spectra-times in the DB {child}\t{clausesTimes[layer]['hits']} vs {clausesTimes[layer]['missed']}")
            continue
        approx = sum(clausesTimes[layer]["time"]) * (
                (1.0 * clausesTimes[layer]["hits"] + clausesTimes[layer]["missed"]) / clausesTimes[layer]["hits"])
        # this is an optimistic approximation :))
        if layer > maxLayer:
            continue
        approxSequenceTime.append((layer, approx))

        filtered = [p for p in uniquePrefixes]
        filtered.extend(clausesTimes[layer]["spectra"])
        prefixesOnly = sorted(filtered, key=lambda x: -len(
            x))  # this is not prefixes only, but the longest and proper prefixes are removed
        for idx, prefix in enumerate(prefixesOnly):
            for j in range(len(prefixesOnly) - 1, idx, -1):
                # if prefixesOnly[j].startswith(prefix):
                if prefix.startswith(prefixesOnly[j]):
                    del prefixesOnly[j]
        uniquePrefixes.update(prefixesOnly)
        minSpectra.append((layer, len(prefixesOnly)))

    result["time"] = sorted([(key, val) for key, val in result["time"].items()], key=lambda t: t[0])

    result["minSpectra"] = minSpectra
    result["approxSequenceTime"] = approxSequenceTime
    result["pipe"] = [(layer, sfinder + wfomc) for (layer, sfinder), (_, wfomc) in
                      zip(result["time"], result["approxSequenceTime"])]
    result["file"] = child
    return result


def fetchIndex(name: str) -> int:
    idx: int = 0
    while True:
        if idx > len(name) or not name[idx].isdigit():
            break
        idx = idx + 1
    return int(name[:idx])


def fillInLegend(current: t.Dict[str, t.Any], prev: t.Optional[t.Dict[str, t.Any]]) -> None:
    # statefully adds legend to current
    if current is None:
        return
    if prev is None:
        current["legend"] = "baseline"
        return

    different = []
    for key, val in current.items():
        if key == "time" or key == "candidates" or key == "index" or "prover9Path" == key or "file" == key \
                or "approxSequenceTime" == key or "minSpectra" == key or "pipe" == key or "version" == key \
                or "initTime" == key or "forkPollSize" == key:
            continue
        if prev[key] != val:
            different.append(key)

    if "tautologyFilter" in different and "contradictionFilter" in different:
        current["legend"] = "tautology + contradiction filter"
    else:
        current["legend"] = " + ".join(different)


def reportSequences(data: t.Dict[str, t.Any]) -> None:
    fileName = data["file"]
    print("reporting statistics from\t{}".format(fileName))

    sentences = set()
    with open(fileName) as file:
        for line in file.readlines():
            if line.startswith("#") or len(line.strip()) == 0:
                continue
            sentence = line.split(";")[0].strip()
            sentences.add(sentence)

    uncomputedSentences = set()
    uniqueSequences = set()

    # if os.path.exists("db.csv"):
    #     sentence_df = pd.read_csv("db.csv")
    # else:
    #     engine = create_engine(future=False)
    #     sentence_df = pd.read_sql_query("SELECT `sequence`.`sequence`,	sentence.sentence_human_readable FROM `sequence` LEFT JOIN sentence ON `sequence`.sentence_id = sentence.id WHERE `sequence`.status = 3", engine)
    engine = create_engine(future=False)
    # sentences = list(e for e in sentences)[:50] # debug
    for idx, sentence in enumerate(sentences):
        if idx % 500 == 0:
            print("{} out of {}".format(idx, len(sentences)))
        sentence_df = pd.read_sql_query(
            "SELECT `sequence`.`sequence` from `sequence` LEFT JOIN sentence ON `sequence`.sentence_id = sentence.id WHERE sentence.sentence_human_readable = \"{}\" and sentence.`skip` = False"
            .format(sentence), engine)
        vals = sentence_df.to_numpy()
        if len(vals) and None != vals[0][0]:
            uniqueSequences.add(vals[0][0])
        else:
            # print("verify\t{}".format(sentence))
            uncomputedSentences.add(sentence)

    prefixesOnly = list(e for e in uniqueSequences)
    prefixesOnly = sorted(prefixesOnly, key=len)
    for idx, prefix in enumerate(prefixesOnly):
        for j in range(len(prefixesOnly) - 1, idx, -1):
            if prefixesOnly[j].startswith(prefix):
                del prefixesOnly[j]

    print("there are {} unique sentences".format(len(sentences)))
    print("there are {} unique sequences".format(len(uniqueSequences)))
    print("there are {} prefix-unique sequences".format(len(prefixesOnly)))
    print("there are {} sentences with no computed sequence".format(len(uncomputedSentences)))
    print("there should be at most {} unique sequences".format(len(sentences) - len(uncomputedSentences)))

    # for u in uniqueSequences:
    #     print(u[:70])


def toSortedList(plotData: t.Dict[int, int]) -> t.List[t.Tuple[int, int]]:
    l = plotData if isinstance(plotData, list) else [(key, value) for key, value in plotData.items()]
    return sorted(l, key=lambda t: t[0])


def grab(targetDir: str, sentenceTime: t.Dict['sentence', float] = None):
    spectra: t.Dict[str, t.Any] = None
    if sentenceTime is None:
        # sentenceTime = loadFailedSpectra(Path(".", "wfomc-errored-sequences.csv"))
        # sentenceTime.update(loadFailedSpectra(Path(".", "wfomc-postponed-sequences.csv")))
        # times, spectra = loadSpectraTimes(Path(".", "sentence_time.csv"))
        # these two are here because we know that everything is either computed or is failed due to some memory reason, etc...
        sentenceTime = {}
        times, spectra = loadSpectraTimesFromFile(Path(".", "sentence_spectrum_time.csv"))
        sentenceTime.update(times)

    print(f"there are {len(sentenceTime)} sentences' times")


    directory = Path(targetDir)
    grabbed: t.List[t.Dict[str, t.Any]] = []
    for child in directory.iterdir():
        if child.name.endswith(".txt") and child.name[0].isdigit() and "sample" not in child.name:
            grabbed.append(readFile(child, sentenceTime, spectra=spectra))

    if not areAllConsistent(grabbed):
        print("data are")
        for data in grabbed:
            print("\t{}".format(data["file"]))
        raise ValueError("inconsistent list of output")

    grabbed = sorted(grabbed, key=lambda data: data['index'])

    if False:
        print("sorting is")
        for g in grabbed:
            print(g["file"])

    for prev, nextE in zip([None] + grabbed, grabbed + [None]):
        fillInLegend(nextE, prev)

    for data in grabbed:
        data["candidates"] = toSortedList(data["candidates"])
        data["time"] = toSortedList(data["time"])
        data["approxSequenceTime"] = toSortedList(
            data["approxSequenceTime"])

    substitution = {"baseline": "variable isomorphism, LB",
                    "decomposableComponents": "baseline",
                    "tautology + contradiction filter": "\\emph{ Tautologies \\& Contradictions }",
                    "isomorphicSentences": "\\emph{Isomorphic Sentences}",
                    "negations": "\\emph{ Negations }",
                    "permutingArguments": "\\emph{ Permuting Arguments }",
                    "reflexiveAtoms": "\\emph{ Reflexive Atoms }",
                    "subsumption": "\\emph{ Subsumption }",
                    "quantifiersReducibility": "$\\theta$*", #%\\emph{ Quantifiers Reducibility }
                    "trivialConstraints": "\\emph{ Trivial Constraints }",
                    "cellGraphPath": "\\emph{ Cell Graph Isomorphism } ",
                    "cellGraph": "\\emph{ Cell Graph Isomorphism } "
                    }

    for data in grabbed:
        data["show"] = True
        data["originalLegend"] = data["legend"]
        data["legend"] = substitution[data["legend"]] if data["legend"] in substitution else data["legend"]

        '''if True: # IJCAI'23
            # appendix setting
            data["show"] = True
            if data["legend"] in ["variable isomorphism", "subsumption"]:
                data["show"] = False
        else:
            # main paper setting
            if data["legend"] in ["baseline", "negations", "permuting arguments", "safe-to-hide except cell graph",
                                  "cell graphs", "isomorphic sentence \& contradictions \& tautoligies",
                                  "all features except cell graph",
                                  "\\emph{ Cell Graph Isomorphism } ",
                                  "all pruning except \\emph{ Cell Graph Isomorphism }",
                                  "\\emph{ Permuting Arguments }",
                                  "\\emph{ Negations }",
                                  "\\emph{Isomorphic Sentences \\& Tautologies \\& Contradictions }",
                                  "baseline", ]:
                data["show"] = True
        '''

    print(
        "\\documentclass{article}\\usepackage{pgfplots}\\pgfplotsset{compat=newest}\\pagestyle{empty}"
        "\\usetikzlibrary{pgfplots.groupplots}\\usepgfplotslibrary{colorbrewer}\\n"
        "\\definecolor{shockingpink}{rgb}{0.99, 0.06, 0.75}"
        "\\definecolor{ao(english)}{rgb}{0.0, 0.5, 0.0}"
        "\\definecolor{palesilver}{rgb}{0.79, 0.75, 0.73}"
        "\\definecolor{navyblue}{rgb}{0.0, 0.0, 0.5}"
        "\\definecolor{mint}{rgb}{0.24, 0.71, 0.54}"
        "\\definecolor{saddlebrown}{rgb}{0.55, 0.27, 0.07}"
        "\\pgfplotscreateplotcyclelist{shortList}{"
        "	{black,thick},% baseline\\n"
        "	{mint},%proving\\n"
        "	{orange},%isomorphic\\n"
        "	{patriarch},%negations\\n"
        "	{shockingpink},%permuting arguments\\n"
        "	{saddlebrown},%Reflexive Atoms\\n"
        "	{palesilver},%Trivial Constraints\\n"
        "	{blue},%subsumptions\\n"
        "	{ao(english),thick},%cellgraph\\n"
        "	{red,thick},%spectra lower bound\\n"
        "}"
        "\\begin{document}\\pgfplotsset{scaled y ticks=false}%")
    print("\\begin{figure}\n")
    print(
        "\\begin{tikzpicture}\\begin{groupplot}[group style={group size=3 by 1},height=6cm,width=7cm,xlabel=layer,cycle list/Dark2,  xticklabels={},  extra x ticks={0,1,2,3,4,5,6,7,8,9,10} ]\n")
    # print("\t\\nextgroupplot[ylabel={\# sentences},ymode=log, xlabel={(a)},cycle list name=shortList,legend style={at={(0.0,1.3)},anchor=north west, legend cell align=left,legend columns=5}]\n")
    print(
        "\t\\nextgroupplot[ylabel={\# sentences},ymode=log, xlabel={(a)},cycle list name=shortList,legend style = {at = {(0.1, 1.1)}, anchor = south west, legend cell  align = left, legend columns = 3}]\n")

    key = "candidates"
    for idx, data in enumerate(grabbed):
        print("\t\t{}\\addplot+[mark=none]	 coordinates {{{}}}; \\addlegendentry{{{}}} %{}".format(
            "" if data["show"] else "%",
            dataToCumulativeCurve(data[key],
                                  division=60 * 60 if key in ["time", "pipe", "approxSequenceTime"] else 1,
                                  # xShift=0 if "approxSequenceTime" == key else 1
                                  ),
            data["legend"],
            data["originalLegend"]))
        if idx == len(grabbed) - 1:
            print("\t\t\\addplot+[mark=none]	 coordinates {{{}}}; \\addlegendentry{{{}}} ".format(
                " ".join(f"({x}, {y})" for x, y in data["minSpectra"]),  # this is already cummulative
                "lower bound spectra"))

    print(
        "\t\\nextgroupplot[ylabel={estimated time [h]}, xshift=0.8cm, xlabel={(b)},cycle list name=shortList]\n")
    key = "pipe"
    for idx, data in enumerate(grabbed):
        print("\t\t{}\\addplot+[mark=none]	 coordinates {{{}}}; %\\addlegendentry{{{}}} %{}".format(
            "" if data["show"] else "%",
            dataToCumulativeCurve(data[key],
                                  division=60 * 60 if key in ["time", "pipe", "approxSequenceTime"] else 1,
                                  #xShift=0 if "approxSequenceTime" == key else 1,
                                  yInitAddition=data["initTime"]),
            data["legend"],
            data["originalLegend"]))

    print("\t\\nextgroupplot[ylabel={time [h]}, xshift=0.8cm, xlabel={(c)},cycle list name=shortList]\n")
    key = "time"
    for idx, data in enumerate(grabbed):
        print("\t\t{}\\addplot+[mark=none]	 coordinates {{{}}}; %\\addlegendentry{{{}}} %{}".format(
            "" if data["show"] else "%",
            dataToCumulativeCurve(data[key],
                                  division=60 * 60 if key in ["time", "pipe", "approxSequenceTime"] else 1,
                                  # xShift=0 if "approxSequenceTime" == key else 1,
                                  yInitAddition=data["initTime"]),
            data["legend"],
            data["originalLegend"]))
    # legend = f"cumulative (a) \# sentences, (b) SFinder+WFOMC time, (c) SFinder time max {grabbed[0]['maxLiteralsPerClause']} literals per clause, max {grabbed[0]['maxClauses']} clauses," \
    #          f" predicates {grabbed[0]['predicates']}, max k {grabbed[0]['maxK']}"
    legend = f"cumulative (a) \# sentences, (b) SFinder+WFOMC time, (c) SFinder time max {grabbed[0]['maxLiteralsPerClause']} literals per clause, max {grabbed[0]['maxClauses']} clauses," \
             f" predicates {grabbed[0]['predicates']}, max k {grabbed[0]['maxK']}"

    print("\\end{groupplot}\\end{tikzpicture}")
    print("\\caption{" + legend + "}\\end{figure}\n")
    print("\\end{document}")
    print("%" + targetDir)


def main(name: str = "", maxLiterals: int = 2, maxClauses: int = 3, unaryPredicates: int = 2, binaryPredicates: int = 2,
         maxLayers: int = -1, k: int = 1, source: str = ""):
    targetDir = "{}-{}-{}-{}-{}-{}-{}".format(name, maxLiterals, maxClauses, maxLayers, unaryPredicates,
                                              binaryPredicates, k)
    if len(source) > 0:
        targetDir = os.path.sep.join([".", source, targetDir])
    else:
        targetDir = os.path.sep.join([".", targetDir])
    print(f"target is {targetDir}")
    grab(targetDir)

    # 1.5.6
    # fo52 --source run5 --name fo52-order4 --maxliterals 5 --maxclauses 2 --maxlayers 10 --unarypredicates 1 --binarypredicates 1 --k 0
    # c52 --source run5 --name c52-order4 --maxliterals 5 --maxclauses 2 --maxlayers 10 --unarypredicates 1 --binarypredicates 1 --k 1

    # c33 --source run5 --name c33-order4 --maxliterals 3 --maxclauses 3 --maxlayers 9 --unarypredicates 2 --binarypredicates 2 --k 1
    # c43 --source run5 --name c43-order4 --maxliterals 4 --maxclauses 3 --maxlayers 12 --unarypredicates 2 --binarypredicates 2 --k 1
    # c44 --source run5 --name c44-order4 --maxliterals 4 --maxclauses 4 --maxlayers 16 --unarypredicates 2 --binarypredicates 2 --k 1


if __name__ == "__main__":
    typer.run(main)
