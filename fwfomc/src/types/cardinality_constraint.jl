
import Base.string

CardinalityRelations = Set([==, >, <, <=, >=])

"""
    CardinalityConstraint

A pair holding a `Predicate` (`String`) and its cardinality.
"""
struct CardinalityConstraint
    pred::Predicate
    k::Int
    op::Function

    function CardinalityConstraint(pred::Predicate, k::Int, op::Function)
        op in CardinalityRelations || DomainError("
            Unsupported function supplied.\n
            Only operations from $CardinalityRelations are supported."
        )

        isequal(op, ==) || ArgumentError("TODO. Only CCs with equality are supported for now.")

        new(pred, k, op)
    end
end

CardinalityConstraint(pred::Predicate, k::Integer) = CardinalityConstraint(pred, k, ==)

predicate(cc::CardinalityConstraint) = cc.pred
cardinality(cc::CardinalityConstraint) = cc.k
operation(cc::CardinalityConstraint) = cc.op

const CC = CardinalityConstraint

(cc::CC)(::Integer) = cc


struct CardinalityConstraintTemplate
    pred::Predicate
    multiplier::Int
    op::Function

    function CardinalityConstraintTemplate(pred::Predicate, k::Int, op::Function)
        op in CardinalityRelations || DomainError("
            Unsupported function supplied.\n
            Only operations from $CardinalityRelations are supported."
        )

        isequal(op, ==) || ArgumentError("TODO. Only CCs with equality are supported for now.")

        new(pred, k, op)
    end
end

const CCTemplate = CardinalityConstraintTemplate

CardinalityConstraintTemplate(pred::Predicate, k::Integer) = CardinalityConstraintTemplate(pred, k, ==)

(cct::CCTemplate)(n::Integer) = CC(cct.pred, cct.multiplier * n, cct.op)



struct Denom 
    k::Int
end

(d::Denom)(::Integer) = d.k

struct ExpDenomTemplate
    k::Int
end

(dt::ExpDenomTemplate)(n::Integer) = factorial(BigInt(dt.k))^n

struct BinomialDenomTemplate
    k::Int
end

(dt::BinomialDenomTemplate)(n::Integer) = binomial(BigInt(n), dt.k)



Base.string(cc::CC) = "{'predicate': ['$(cc.pred[1])', $(cc.pred[2])], 'cardinality': '$(cc.k)', 'op': '$(cc.op)'}"
Base.string(cc::CCTemplate) = "{'predicate': ['$(cc.pred[1])', $(cc.pred[2])], 'cardinality': '$(cc.multiplier)*n', 'op': '$(cc.op)'}"
Base.string(d::Denom) = "$(d.k)"
Base.string(d::ExpDenomTemplate) = "$(factorial(factorial(BigInt(d.k))))^n"
Base.string(d::BinomialDenomTemplate) = "binom(n, $(d.k))"
