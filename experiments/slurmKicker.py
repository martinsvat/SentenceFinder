import io
import os
import time
from pathlib import Path

import typer
import typing as t

# SET THIS UP
SFINDER_JAR = "/home/MY_USER_NAME/SentenceFinder/SFinder.jar"
PATH_TO_JULIA_SCRIPT = "/home/MY_USER_NAME/SentenceFinder/julia/sample_multithreaded_unskolemized.jl"
PATH_TO_JULIA_INSTALL = "/home/MY_USER_NAME/SentenceFinder/julia/sampleInstall.jl"
PATH_TO_PROVER9 = "/home/MY_USER_NAME/LADR-2009-11A/bin/prover9"
N_JULIA_THREADS = 30
TIME_LIMIT = 2880
TASK_TIME = "71:59:59"
# END OF SETUP

def order4(maxLiterals: int, maxClauses: int, unaryPredicates: int, binaryPredicates: int, maxLayers: int, k: int) -> \
        t.Callable[[], t.Dict[str, t.Union[str, int]]]:
    def gen():
        base = {"-Dida.sentenceSetup.maxOverallLiterals": maxLayers if maxLayers > 0 else maxLiterals * maxClauses,
                "-Dida.sentenceSetup.maxClauses": maxClauses,
                "-Dida.sentenceSetup.maxLiteralsPerClause": maxLiterals,
                "-Dida.sentenceSetup.unaryPredicates": unaryPredicates,
                "-Dida.sentenceSetup.binaryPredicates": binaryPredicates,
                "-Dida.sentenceSetup.quantifiers": "true",
                "-Dida.sentenceSetup.maxK": k,
                "-Dida.sentenceSetup.maxCountingClauses": maxClauses,
                "-Dida.sentenceSetup.maxLiteralsPerCountingClause": 1,
                "-Dida.sentenceSetup.doubleCountingExist": "false",
                "-Dida.sentenceSetup.prover9Path": "none",  # "/usr/bin/prover9",
                "-Dida.sentenceSetup.maxProver9Seconds": 30,
                "-Dida.sentenceSetup.naiveTautology": "false",
                "-Dida.sentenceSetup.tautologyFilter": "false",
                "-Dida.sentenceSetup.contradictionFilter": "false",
                "-Dida.sentenceSetup.countingContradictionFilter": "false",
                "-Dida.sentenceSetup.decomposableComponents": "false",
                "-Dida.sentenceSetup.isomorphicSentences": "false",
                "-Dida.sentenceSetup.negations": "false",
                "-Dida.sentenceSetup.permutingArguments": "false",
                "-Dida.sentenceSetup.reflexiveAtoms": "false",
                "-Dida.sentenceSetup.subsumption": "false",
                "-Dida.sentenceSetup.quantifiersReducibility": "false",
                "-Dida.sentenceSetup.trivialConstraints": "false",
                "-Dida.sentenceSetup.cellGraph": "none",
                }
        base["out"] = "baseline.txt"
        yield base

        base = base.copy()
        base["-Dida.sentenceSetup.decomposableComponents"] = "true"
        base["out"] = "baseline_decomposable.txt"
        yield base

        base = base.copy()
        base["-Dida.sentenceSetup.prover9Path"] = PATH_TO_PROVER9
        base["-Dida.sentenceSetup.naiveTautology"] = "true"
        base["-Dida.sentenceSetup.tautologyFilter"] = "true"
        base["-Dida.sentenceSetup.contradictionFilter"] = "true"
        # base["-Dida.sentenceSetup.countingContradictionFilter"] = "true"
        base["out"] = "baseline_decomposable_proving.txt"
        yield base

        base = base.copy()
        base["-Dida.sentenceSetup.isomorphicSentences"] = "true"
        base["out"] = "baseline_decomposable_proving_isoSent.txt"
        yield base

        base = base.copy()
        base["-Dida.sentenceSetup.negations"] = "true"
        base["out"] = "baseline_decomposable_proving_isoSent_isoNeg.txt"
        yield base

        base = base.copy()
        base["-Dida.sentenceSetup.permutingArguments"] = "true"
        base["out"] = "baseline_decomposable_proving_isoSent_isoNeg_permArg.txt"
        yield base

        base = base.copy()
        base["-Dida.sentenceSetup.reflexiveAtoms"] = "true"
        base["out"] = "baseline_decomposable_proving_isoSent_isoNeg_permArg_reflexAtoms.txt"
        yield base

        base = base.copy()
        base["-Dida.sentenceSetup.trivialConstraints"] = "true"
        base[
            "out"] = "baseline_decomposable_proving_isoSent_isoNeg_permArg_reflexAtoms_trivialConstraints.txt"
        yield base

        base = base.copy()
        base["-Dida.sentenceSetup.subsumption"] = "true"
        base["out"] = "baseline_decomposable_proving_isoSent_isoNeg_permArg_reflexAtoms_trivialConstraints_subsumption.txt"
        yield base

        base = base.copy()
        base["-Dida.sentenceSetup.quantifiersReducibility"] = "true"
        base["out"] = "baseline_decomposable_proving_isoSent_isoNeg_permArg_reflexAtoms_trivialConstraints_subsumption_quantifiers.txt"
        yield base

        base = base.copy()
        base["-Dida.sentenceSetup.cellGraph"] = PATH_TO_JULIA_SCRIPT
        base[
            "out"] = "baseline_decomposable_proving_isoSent_isoNeg_permArg_reflexAtoms_trivialConstraints_subsumption_quantifiers_cell.txt"
        yield base

    return gen

def slurm(generator: t.Callable[[], t.Dict[str, t.Union[str, int]]], targetDir: str, maxMemory: int) -> None:
    directory = Path(targetDir)
    directory.mkdir(exist_ok=True, parents=True)

    commands: t.List[t.Tuple[str, str]] = []
    for config in generator():
        # sentences_file = directory / "{}{}".format(len(commands), config["out"])
        sentences_file = str(directory) + "/" + "{}{}".format(len(commands), config["out"])
        shName = directory.name + "_" + "{}{}.sh".format(len(commands), config["out"])
        commands.append((
            "java -Xms5g -Xmx{}g -Dida.sentenceSetup.timeLimit={} ".format(maxMemory, TIME_LIMIT)
            + " ".join(f"{k}={v}" for k, v in config.items() if k.startswith("-D"))
            + " -Djava.util.concurrent.ForkJoinPool.common.parallelism=10"
            + " -Dida.sentenceSetup.statesStore=false"
            + f" -Dida.sentenceSetup.juliaThreads={N_JULIA_THREADS}"
            + f" -jar {SFINDER_JAR}"
            + f" > {sentences_file}",
            shName
        )
        )

    for idx, (command, shName) in enumerate(commands):
        with open(shName, 'w') as f:
            f.write("#!/bin/bash\n"
                    "#SBATCH --partition=cpulong \n"
                    "#SBATCH --time={TASK_TIME}\n"
                    "#SBATCH --nodes=1\n"
                    "#SBATCH --ntasks-per-node=1\n"
                    "#SBATCH --cpus-per-task=1\n"
                    f"#SBATCH --mem={maxMemory + 10}g\n"
                    f"echo \"{command}\"\n"
                    f"echo \"origin is {shName}\"\n"
                    "ml Java/17.0.4\n"
                    )
            if "sample_multithreaded_unskolemized.jl" in command:
                f.write("ml Julia/1.8.5-linux-x86_64\n"
                        f"julia {PATH_TO_JULIA_INSTALL}\n")
            f.write(command)

    for idx, (command, shName) in enumerate(commands):
        print(f"sbatch {shName}")


def main(name: str = "r1", maxLiterals: int = 2, maxClauses: int = 2, unaryPredicates: int = 2,
         binaryPredicates: int = 2, k: int = 1, generator: str = "order4", maxMemory: int = 50, maxLayers: int = -1):
    configs = {"order4": order4(maxLiterals=maxLiterals, maxClauses=maxClauses, unaryPredicates=unaryPredicates,
                                binaryPredicates=binaryPredicates, maxLayers=maxLayers, k=k),

               }
    targetDir = "{}-{}-{}-{}-{}-{}-{}-{}".format(name, generator, maxLiterals, maxClauses, maxLayers, unaryPredicates,
                                                 binaryPredicates, k)

    slurm(configs[generator], targetDir=targetDir, maxMemory=maxMemory)


if __name__ == "__main__":
    typer.run(main)
