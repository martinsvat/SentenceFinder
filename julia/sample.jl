using Pkg

# # Use current folder as a Julia project
Pkg.activate(".")

# # Add FastWFOMC.jl dependency to the current Julia project
# Pkg.add(PackageSpec(url="https://github.com/jan-toth/FastWFOMC.jl"))

# # Install all dependencies that might be missing
# Pkg.instantiate()

using FastWFOMC

open(ARGS[1]) do fr
    for line in readlines(fr)
        startswith(line, '#') && continue
        cell_graph = get_cell_graph(line)
        println(cell_graph)
    end
end
