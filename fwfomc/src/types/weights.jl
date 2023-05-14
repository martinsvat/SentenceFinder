const _NemoPolynomial = Union{fmpz_poly,fmpq_poly,fmpz_mpoly,fmpq_mpoly}
const _NemoNumber = Union{fmpz, fmpq}
const _NemoType = Union{_NemoPolynomial, _NemoNumber}

const WFOMCWeightsType = Union{Number, _NemoType}


"""
    PredicateWeights{T<:WeightsTypes}

Named pair of positive weight 'w' and a negative weight 'w̄'.
"""
const PredicateWeights{T<:WFOMCWeightsType} = @NamedTuple {w::T, w̄::T}

PredicateWeights(w::T, w̄::T) where {T<:WFOMCWeightsType} = PredicateWeights((w, w̄))
PredicateWeights(weights::Tuple{T,T}) where {T<:WFOMCWeightsType} = PredicateWeights{T}(weights)

function Base.convert(::Type{PredicateWeights{T}}, tuple::Tuple{U,V}) where {T<:WFOMCWeightsType,U<:WFOMCWeightsType,V<:WFOMCWeightsType}
    PredicateWeights{T}(convert.(T, tuple))
end


"""
    WFOMCWeights{T<:WeightsTypes}

Dictionary of Predicate (String) keys. Each is assigned a named pair of values, i.e.,
positive weight 'w' and a negative weight 'w̄'.
"""
const WFOMCWeights{T<:WFOMCWeightsType} = Dict{Predicate,PredicateWeights{T}}

WFOMCWeights() = WFOMCWeights{Rational{BigInt}}()

function WFOMCWeights(pairs::Pair{Predicate,PredicateWeights{T}}...) where {T<:WFOMCWeightsType}
    WFOMCWeights{T}(pairs...)
end

function WFOMCWeights(pairs::Pair{Predicate,Tuple{T,T}}...) where {T<:WFOMCWeightsType}
    WFOMCWeights{T}(map(x -> x.first => PredicateWeights(x.second), pairs)...)
end

const _PairsType = Pair{Predicate,Tuple{A,B}} where {A<:WFOMCWeightsType,B<:WFOMCWeightsType}
function WFOMCWeights(pairs::_PairsType...)
    T = promote_type(typeof.(first(pairs).second)...)
    for (_, second) in Iterators.drop(pairs, 1)
        T = promote_type(T, typeof.(second)...)
    end

    WFOMCWeights{T}(map(x -> x.first => PredicateWeights{T}(x.second), pairs)...)
end

function WFOMCWeights(ring, w::Dict)
    T = typeof(one(ring))
    WFOMCWeights{T}(k => PredicateWeights{T}(ring.(v)) for (k, v) in w)
end

"""
    fill_missing_weights!(weights::WFOMCWeights{T}, ψ::Expression, val::T)

Sets both positive and negative weight of each predicate in `ψ` that is not present
in `weights`, to `val`.
If `val` is unset, it defaults to one.
"""
function fill_missing_weights!(weights::WFOMCWeights{T}, ψ::Formula, val::T = one(weights)) where {T}
    for predicate in predicate_symbols(ψ)
        if !haskey(weights, predicate)
            weights[predicate] = PredicateWeights(val, val)
        end
    end
end


Base.zero(x::_NemoPolynomial) = parent(x)(0)
Base.one(x::_NemoPolynomial) = parent(x)(1)
Base.:/(x::T, y::T) where {T<:_NemoType} = x // y


Base.zero(::WFOMCWeights{T}) where {T<:Number} = zero(T)
Base.zero(::WFOMCWeights{T}) where {T<:_NemoNumber} = T(0)
Base.zero(weights::WFOMCWeights{T}) where {T<:_NemoPolynomial} = zero(_get_nemo_ring(weights))

Base.zeros(weights::WFOMCWeights, dims...) = fill(zero(weights), dims...)

Base.one(::WFOMCWeights{T}) where {T<:Number} = one(T)
Base.one(::WFOMCWeights{T}) where {T<:_NemoNumber} = T(1)
Base.one(weights::WFOMCWeights{T}) where {T<:_NemoPolynomial} = one(_get_nemo_ring(weights))

Base.ones(weights::WFOMCWeights, dims...) = fill(one(weights), dims...)


function _get_nemo_ring(weights::WFOMCWeights{T}) where {T<:_NemoPolynomial}
    weights |> first |> x -> x.second.w |> parent
end
