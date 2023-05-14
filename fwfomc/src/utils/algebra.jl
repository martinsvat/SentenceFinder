"""
    Symmetric

A simple straightforward implementation of a symmetric matrix.
"""
struct Symmetric{T} <: AbstractMatrix{T}
    data::Matrix{T}
    uplo::Char

    function Symmetric(data::AbstractMatrix{T}, uplo::Char = 'U') where {T}
        uplo == 'U' || uplo == 'L' || throw(ArgumentError("uplo argument must be either 'U' (upper) or 'L' ('L')"))
        new{T}(data, uplo)
    end
end

@inline function Base.getindex(A::Symmetric, i::Integer, j::Integer)
    @boundscheck checkbounds(A, i, j)
    @inbounds if (A.uplo == 'U') == (i <= j)
        return A.data[i, j]
    else
        return A.data[j, i]
    end
end

# import Base: size
Base.size(A::Symmetric, d) = size(A.data, d)
Base.size(A::Symmetric) = size(A.data)
