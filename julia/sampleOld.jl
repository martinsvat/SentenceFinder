using Pkg
Pkg.activate(".")
using FastWFOMC

println(ARGS[1])
print(get_cell_graph(ARGS[1]))
