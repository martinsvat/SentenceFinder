using Pkg
using Base.Threads

Pkg.activate("."; io=devnull)
using FastWFOMC

function process_sentences(file=ARGS[1], limit_cg=30)
    if length(ARGS) > 1 
        limit_cg = parse(Int, ARGS[2])
    end

    lines = String[]
    open(file) do fr
        append!(lines, readlines(fr))
    end

    sentences = fill("#", length(lines))

    Threads.@threads for i in eachindex(lines)
        line = lines[i]
        startswith(line, '#') && continue
        sentences[i] = get_cell_graph_unskolemized(line; limit_cg)
    end

    for sentence in sentences
        startswith(sentence, '#') && continue
        println(sentence)
    end
end

process_sentences()