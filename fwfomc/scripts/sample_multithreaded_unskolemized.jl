# using Pkg
# Pkg.activate("."; io=devnull)

using Base.Threads
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
        sentences[i] = get_cell_graph_unskolemized(line)
    end

    for sentence in sentences
        startswith(sentence, '#') && continue
        println(sentence)
    end
end

process_sentences()
