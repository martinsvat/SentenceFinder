using Pkg
using Base.Threads

# # Use current folder as a Julia project
Pkg.activate("."; io=devnull)

# # Add FastWFOMC.jl dependency to the current Julia project
# Pkg.add(PackageSpec(url="https://github.com/jan-toth/FastWFOMC.jl"))

# # Install all dependencies that might be missing
# Pkg.instantiate()

using FastWFOMC

function process_sentences(file=ARGS[1])
    lines = String[]
    open(file) do fr
        append!(lines, readlines(fr))
    end

    sentences = fill("#", length(lines))

    Threads.@threads for i in eachindex(lines)
        line = lines[i]
        startswith(line, '#') && continue
        sentences[i] = get_cell_graph(line)
    end

    for sentence in sentences
        startswith(sentence, '#') && continue
        println(sentence)
    end
end

process_sentences()
