# using Pkg
# Pkg.activate("."; io=devnull)
# Pkg.instantiate(io=devnull)

using FastWFOMC

function process_sentences(file=ARGS[1], n=10)
    if length(ARGS) > 1
        n = parse(Int, ARGS[2])
    end

    open(file) do fr
        
        for line in readlines(fr)
            startswith(line, '#') && continue  # filter out comments

            seq = zeros(BigInt, n)
            for i = 1:n
                wfomc = compute_wfomc_unskolemized(line, i) 
                seq[i] = numerator(wfomc)
            end
            
            println(line, ";", join(seq, ", "))
        end
    
    end
end

process_sentences()
