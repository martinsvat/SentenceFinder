mutable struct Cache
    cache::LRU

    misses::Int
    total::Int

    Cache(maxsize = 10_000) = new(LRU(; maxsize), 0, 0)
end

function Base.empty!(cache::Cache)
    empty!(cache.cache)
    cache.misses = 0
    cache.total = 0
end

function Base.get!(f::Function, cache::Cache, key)
    cache.total += 1
    get!(cache.cache, key) do
        cache.misses += 1
        cache.cache[key] = f()
    end
end

function Base.show(io::IO, cache::Cache)
    print(io, "\tCache hits:\t$(cache.total-cache.misses)\n")
    print(io, "\tCache misses:\t$(cache.misses)")
end

struct TermCaches
    dterm::Cache
    jterm::Cache

    TermCaches(maxsize = 10_000) = new(Cache(maxsize), Cache(maxsize))
end

function Base.empty!(cache::TermCaches)
    empty!(cache.dterm)
    empty!(cache.jterm)
end

function Base.show(io::IO, cache::TermCaches)
    join(io, ("Get_$(name)_Term:\n$(store)" for (name, store) in [("D", cache.dterm), ("J", cache.jterm)]), '\n')
end

CACHE = TermCaches()
