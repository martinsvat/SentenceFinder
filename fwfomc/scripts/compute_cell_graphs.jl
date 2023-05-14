# using Pkg
# Pkg.activate("."; io=devnull)
# Pkg.instantiate(io=devnull)

using FastWFOMC

function process_sentences(file=ARGS[1])
    open(file) do fr
        
        for line in readlines(fr)
            startswith(line, '#') && continue  # filter out comments
            cg = get_cell_graph_unskolemized(line)
            println(line, ";", cg)
        end
    
    end
end

process_sentences()
