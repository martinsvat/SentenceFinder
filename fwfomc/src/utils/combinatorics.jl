struct PascalTriangle{T<:Signed}
    data::Vector{Vector{T}}

    function PascalTriangle{T}(height::Integer) where {T}
        height < 0 && throw(DomainError("Height of the Pascal triangle must be non-negative! It was $height"))
        pt = Vector{Vector{T}}(undef, height + 1)
        pt[1] = [1]
        prev_line = pt[1]

        for n = 1:height
            line = Vector{T}(undef, n + 1)
            line[1] = 1
            for k = 1:n-1
                line[k+1] = prev_line[k] + prev_line[k+1]
            end

            line[n+1] = 1
            pt[n+1] = line
            prev_line = line
        end

        return new{T}(pt)
    end
end

PascalTriangle(height::Integer) = PascalTriangle{BigInt}(height)
Base.length(pt::PascalTriangle) = length(pt.data)
Base.getindex(pt::PascalTriangle, n::Integer, k::Integer) = pt.data[n+1][k+1]

mybinomial(n::Integer, k::Integer) = Base.binomial(n, k)
mybinomial(::Nothing, n::Integer, k::Integer) = Base.binomial(n, k)

function mybinomial(pt::PascalTriangle, n::Integer, k::Integer)
    n < k && return 0
    return pt[n, k]
end

mymultinomial(ks::Integer...) = Combinatorics.multinomial(ks...)
mymultinomial(::Nothing, ks::Integer...) = Combinatorics.multinomial(ks...)

function mymultinomial(pt::PascalTriangle, ks::Integer...)
    ret = one(typeof(ks[begin]))
    for (k, n) in zip(ks, cumsum(ks))
        ret *= mybinomial(pt, n, k)
    end
    return ret
end

mymultiexponents(n::Integer, k::Integer) = Combinatorics.multiexponents(k, n)
