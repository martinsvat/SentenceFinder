module FastWFOMC

using LightGraphs
using Nemo
using Pkg
using TOML 


import LinearAlgebra

include("utils/utils.jl")
using .utils

export compute_wfomc, compute_wfomc_unskolemized, WFOMCWeights, CardinalityConstraint
export NoOptFastWFOMCAlgorithm, FastWFOMCAlgorithm
export fill_missing_weights!
export Formula, parse_formula, is_satisfiable
export get_cell_graph, get_cell_graph_unskolemized, get_skolemized_formula

include("logic/logic.jl")
include("logic/reductions.jl")
include("types/types.jl")
include("cells.jl")
include("wmc.jl")
include("algorithm.jl")

function get_version()
    return TOML.parsefile(joinpath(dirname(@__DIR__), "Project.toml"))["version"]
end

end # module
