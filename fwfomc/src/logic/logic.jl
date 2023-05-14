include("aima/aimalogic.jl")
using .aimalogic

const Formula = Expression
const parse_formula = expr
const Variable(name::String) = Formula(name)
const Predicate = Tuple{String,Int}


TRUE = Formula("TRUE")
FALSE = Formula("FALSE")


function is_satisfiable(ψ::Formula)
    sat = dpll_satisfiable(ψ)
    return sat !== false
end

function replace_subformula(ψ::Formula, d::Dict{Predicate, Formula})
    pred = (ψ.operator, length(ψ.arguments))
    if haskey(d, pred)
        return d[pred]
    else
        return Formula(ψ.operator, [replace_subformula(arg, d) for arg in ψ.arguments]...)
    end
end


"""
    PartialModel

AIMA implementation of the DPLL algorithm may return only a partial assignment
(of propositional symbols to truth values) as a solution,
basically returning multiple (implicit) models in one return value.

This structure allows to iterate over all those models.
If DPLL returned a complete assignment, the iterator has only one element, i.e., the
returned model.
"""
struct PartialModel
    assignment::Dict{Formula,Bool}
    unassigned_symbols::Set{Formula}
end


"""
    ModelIterator

Iterator over all models for a SAT problem.
"""
struct ModelIterator
    partial_models::Vector{PartialModel}
end

function Base.iterate(iter::ModelIterator, state = (1, 0))
    # binary of 's' encodes true/false for each unassigned symbol in the partial model
    model_idx, s = state
    model_idx > length(iter.partial_models) && return nothing

    partial_model = iter.partial_models[model_idx]
    n = length(partial_model.unassigned_symbols)

    model = copy(partial_model.assignment)
    for (prop, value) in zip(partial_model.unassigned_symbols, last(bitstring(s), n))
        model[prop] = parse(Bool, value)
    end

    next_state = s < 2^n - 1 ? (model_idx, s + 1) : (model_idx + 1, 0)
    return (model, next_state)
end

Base.IteratorEltype(::ModelIterator) = Base.HasEltype()
Base.eltype(::ModelIterator) = Dict{Formula,Bool}
Base.IteratorSize(::ModelIterator) = Base.HasLength()
Base.length(iter::ModelIterator) = length(iter.partial_models) > 0 ? sum(2^length(m.unassigned_symbols) for m in iter.partial_models) : 0

function find_all_models(ψ::Formula)
    clauses = conjuncts(to_conjunctive_normal_form(ψ))
    symbols_set = proposition_symbols(ψ)
    symbols = collect(symbols_set)

    models = PartialModel[]
    while true
        model = dpll(clauses, symbols, Dict{Formula,Bool}())
        isa(model, Dict) || break

        # Make sure, there are no trivial assignments in the model
        delete!(model, TRUE)
        delete!(model, FALSE)

        # create iterator over all implied models
        push!(models, PartialModel(model, setdiff(symbols_set, keys(model))))

        # add negation of the found model to the clauses of ψ
        push!(clauses, reduce(|, (value ? ~symbol : symbol for (symbol, value) in model); init=FALSE))
    end

    return ModelIterator(models)
end
