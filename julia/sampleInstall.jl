using Pkg

# Use current folder as a Julia project
Pkg.activate(".")

# Add FastWFOMC.jl dependency to the current Julia project
Pkg.add(PackageSpec(url="https://github.com/jan-toth/FastWFOMC.jl"))
Pkg.instantiate()
using FastWFOMC

println(ARGS[1])
print(get_cell_graph(ARGS[1]))

#cell_graph = get_cell_graph("(~B0(x, y) | S0(x))")
#println(cell_graph)
