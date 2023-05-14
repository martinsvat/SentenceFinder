function wmc(ψ::Expression, weights::WFOMCWeights; evidence = nothing)
    if evidence === nothing
        return _wmc(ψ, weights)
    else
        return _wmc_with_evidence(ψ, weights, evidence)
    end
end

function _wmc_with_evidence(ψ::Expression, weights::WFOMCWeights, evidence)
    wmc = zero(weights)

    for model in find_all_models(ψ)
        model_weight = one(weights)

        for (symbol, value) in model
            if symbol ∉ evidence
                model_weight *= weights[(symbol.operator, length(symbol.arguments))][value ? 1 : 2]
            end
        end

        wmc += model_weight
    end

    return wmc
end

function _wmc(ψ::Formula, weights::WFOMCWeights)
    wmc = zero(weights)

    for model in find_all_models(ψ)
        model_weight = one(weights)

        for (symbol, value) in model
            model_weight *= weights[symbol.operator][value ? 1 : 2]
        end

        wmc += model_weight
    end

    return wmc
end
