function get_skolemized_formula(φ::AbstractString)
    Γ, weights, ccs, denoms = skolemize_theory(φ)

    ψ = reduce(&, Γ) |> string
    
    weights_str = []
    for ((name, arity), (pos, neg)) in weights
        push!(weights_str, "{'predicate': ['$name', $arity], 'weight': [$pos, $neg]}")
    end

    ccs_str = []
    for cc in ccs
        push!(ccs_str, string(cc))
    end

    denom_str = []
    for denom in denoms
        push!(denom_str, string(denom))
    end

    postprocess = arr -> "[" * join(arr, ", ") * "]"

    return ψ, weights_str |> postprocess, ccs_str |> postprocess, denom_str |> postprocess
end

function skolemize_theory(Γ::AbstractString, weights=Dict())
    data = Dict(
        :skolem => 1,
        :counting => 1,
        :ccs => [],
        :denoms => [],
        :weights => weights,
        :ks => [])

        # TODO handle k == 0

    Γ = split(Γ, " & ")
    newΓ = []

    for sentence in Γ
        conjs = _process_quantified_sentence(sentence; data)
        push!(newΓ, conjs...)
    end

    return newΓ, weights, data[:ccs], data[:denoms], data[:ks]
end


function _process_quantified_sentence(sentence; vars=["x", "y"], data)
    if startswith(sentence, "(")
        sentence = sentence[2:end-1]
    end

    first = _detect_one_quantifier(sentence; var=vars[1])
    second = _detect_one_quantifier(first[2]; var=vars[2])
    ϕ = parse_formula(second[2] |> String)

    if first[1] == 1
        
        if second[1] == 0
            return _handle_forall(ϕ; vars, data)
        elseif second[1] == 1
            return _handle_forall_forall(ϕ; vars, data)
        elseif second[1] == 2
            return _handle_forall_exists(ϕ; vars, data)
        else # second[1] == 3
            # V E=
            k = second[3]
            push!(data[:ks], k)
            return _handle_forall_existsK(ϕ, k; vars, data)
        end
    
    elseif first[1] == 2
        
        if second[1] == 0
            return _handle_exists(ϕ; vars, data)
        elseif second[1] == 1
            return _handle_exists_forall(ϕ; vars, data)
        elseif second[1] == 2
            return _handle_exists_exists(ϕ; vars, data)
        else # second[1] == 3
            # E E=
            k = second[3]
            push!(data[:ks], k)
            return _handle_exists_existsK(ϕ, k; vars, data)
        end
    else # first[1] == 3
        
        k1 = first[3]
        push!(data[:ks], k1)

        if second[1] == 0
            # E=    
            return _handle_existsK(ϕ, k1; vars, data)
        elseif second[1] == 1
            # E= V
            return _handle_existsK_forall(ϕ, k1; vars, data)
        elseif second[1] == 2
            # E= E
            return _handle_existsK_exists(ϕ, k1; vars, data)
        else # second[1] == 3
            # E= E=
            k2 = second[3]
            push!(data[:ks], k2)
            return _handle_existsK_existsK(ϕ, k1, k2; vars, data)
        end
    end
end

function _detect_one_quantifier(subformula; var="x")
    if subformula[1:2+length(var)+1] == "V $var "
        return 1, subformula[5:end]
    elseif subformula[1:2+length(var)+1] == "E $var "
        return 2, subformula[5:end]
    elseif subformula[1:2] == "E="
        i = 3
        while isdigit(subformula[i])
            i += 1
        end
        k = parse(Int, subformula[3:i-1])
        startswith(subformula[i:end], " $var ") || error("Counting quantifier formatted unexpectedly.")
        return 3, subformula[(i+1+length(var)+1):end], k
    else
        return 0, subformula
    end
end

function _handle_forall(ϕ; vars, data)
    # println("V")
    # println(ϕ)
    return [ϕ]
end

function _handle_exists(ϕ; vars, data)
    cnt = data[:skolem]

    S = parse_formula("S$(cnt)")
    ψs = to_conjunctive_normal_form(~ϕ | S)  |> conjuncts

    data[:weights][("S$(cnt)", 0)] = (1, -1)

    data[:skolem] += 1
    return ψs
end

function _handle_forall_forall(ϕ; vars, data)
    # println("V V")
    # println(ϕ)
    return [ϕ]
end

function _handle_forall_exists(ϕ; vars, data)
    cnt = data[:skolem]

    S = parse_formula("S$(cnt)($(vars[1]))")
    ψs = to_conjunctive_normal_form(~ϕ | S) |> conjuncts
    # println("V E")
    # println(ϕ)
    data[:weights][("S$(cnt)", 1)] = (1, -1)

    data[:skolem] += 1
    return ψs
end

function _handle_exists_forall(ϕ; vars, data)
    cnt = data[:skolem]

    S0 = parse_formula("S$(cnt)")
    S1 = parse_formula("S$(cnt)($(vars[1]))")
    ψs = [ϕ | S1, ~S0 | S1]
    # println("E V")
    # println(ϕ)
    data[:weights][("S$(cnt)", 0)] = (1, -1)
    data[:weights][("S$(cnt)", 1)] = (1, -1)
    
    data[:skolem] += 1
    return ψs
end

function _handle_exists_exists(ϕ; vars, data)
    cnt = data[:skolem]

    S = parse_formula("S$(cnt)")
    ψs = to_conjunctive_normal_form(~ϕ | S) |> conjuncts
    # println("E E")
    # println(ϕ)
    data[:weights][("S$(cnt)", 0)] = (1, -1)

    data[:skolem] += 1
    return ψs
end


# TODO handle k == 0

function _handle_existsK(ϕ, k; vars, data)
    # TODO
    # if is_logic_proposition_symbol(ϕ.operator)
    # Here, I could only introduce a CC
    cnt = data[:counting]

    Rx = parse_formula("R$cnt($(vars[1]))")
    cnjs = to_conjunctive_normal_form(Expression("<=>", ϕ, Rx)) |> conjuncts

    push!(data[:ccs], CC((Rx.operator, 1), k))
    data[:weights][(Rx.operator, 1)] = (1, 1)

    data[:counting] += 1

    return cnjs
end

function _handle_forall_existsK(ϕ, k; vars, data)
    sk_cnt = data[:skolem]
    count_cnt = data[:counting]

    Rxy = parse_formula("R$count_cnt($(vars[1]), $(vars[2]))")
    Fxy = [parse_formula("F$(count_cnt)_$(i)($(vars[1]), $(vars[2]))") for i = 1:k]
    Sx = [parse_formula("S$(sk_cnt)_$(i)($(vars[1]))") for i = 1:k]

    cnjs = to_conjunctive_normal_form(Expression("<=>", ϕ, Rxy)) |> conjuncts
    append!(cnjs, to_conjunctive_normal_form(Expression("<=>", Rxy, reduce(|, Fxy))) |> conjuncts)
    for (f, s) in zip(Fxy, Sx)
        push!(cnjs, ~f | s)

        data[:weights][(f.operator, 2)] = (1, 1)
        data[:weights][(s.operator, 1)] = (1, -1)
    end
    for i = 1:k
        for j = (i+1):k
            push!(cnjs, ~Fxy[i] | ~Fxy[j])
        end
    end

    data[:weights][(Rxy.operator, 2)] = (1, 1)
    push!(data[:ccs], CCTemplate((Rxy.operator, 2), k))

    push!(data[:denoms], ExpDenomTemplate(k))
    
    data[:skolem] += 1
    data[:counting] += 1
    
    return cnjs
end

function _handle_existsK_forall(ϕ, k; vars, data)
    sk_cnt = data[:skolem]
    count_cnt = data[:counting]

    Px = parse_formula("P$count_cnt($(vars[1]))")
    Sx = parse_formula("S$sk_cnt($(vars[1]))")
    
    cnjs = to_conjunctive_normal_form(~Px | ϕ) |> conjuncts
    append!(cnjs, to_conjunctive_normal_form(ϕ | Sx) |> conjuncts)
    push!(cnjs, ~Px | Sx)

    data[:weights][(Px.operator, 1)] = (1, 1)
    data[:weights][(Sx.operator, 1)] = (1, -1)
    push!(data[:ccs], CC((Px.operator, 1), k))

    data[:skolem] += 1
    data[:counting] += 1

    return cnjs
end

function _handle_exists_existsK(ϕ, k; vars, data)
    error("Unsupported quantifier constellation")

    sk_cnt = data[:skolem]
    count_cnt = data[:counting]
    data[:skolem] += 1
    data[:counting] += 1

    Cx = parse_formula("C$count_cnt($(vars[1]))")
    Dx = parse_formula("D$count_cnt($(vars[1]))")
    S = parse_formula("S$sk_cnt")

    cnjs = _handle_lemma4(Cx & Dx, ϕ, k; vars, data)
    push!(cnjs, Cx | S)
    push!(cnjs, Cx | Dx)

    data[:weights][(Cx.operator, 1)] = (1, 1)
    data[:weights][(Dx.operator, 1)] = (1, -1)
    data[:weights][(S.operator, 0)] = (1, -1)
    return cnjs
end

function _handle_existsK_exists(ϕ, k; vars, data)
    error("Unsupported quantifier constellation")

    sk_cnt = data[:skolem]
    count_cnt = data[:counting]

    Rx = parse_formula("R$count_cnt($(vars[1]))")
    Sx = parse_formula("S$sk_cnt($(vars[1]))")

    cnjs = to_conjunctive_normal_form(~ϕ | Rx) |> conjuncts
    append!(cnjs, to_conjunctive_normal_form(~ϕ | Sx) |> conjuncts)
    push!(cnjs, Rx | Sx)


    push!(data[:ccs], CC((Rx.operator, 1), k))
    data[:weights][(Rx.operator, 1)] = (1, 1)
    data[:weights][(Sx.operator, 1)] = (1, -1)

    data[:skolem] += 1
    data[:counting] += 1

    return cnjs
end

function _handle_existsK_existsK(ϕ, k1, k2; vars, data)
    error("Unsupported quantifier constellation")

    count_cnt = data[:counting]
    data[:counting] += 1

    Rx = parse_formula("Rx$count_cnt($(vars[1]))")
    Rxy = parse_formula("Rxy$count_cnt($(vars[1]), $(vars[2]))")
    Cx = parse_formula("C$count_cnt($(vars[1]))")
    Dx = parse_formula("D$count_cnt($(vars[1]))")

    data[:weights][(Cx.operator, 1)] = (1, 1)
    data[:weights][(Dx.operator, 1)] = (1, -1)
    
    cnjs = to_conjunctive_normal_form(Expression("<=>", ϕ, Rxy)) |> conjuncts
    append!(cnjs, _handle_lemma4(~Rx, Rxy, k2; vars, data))
    push!(cnjs, Rx | Cx)
    push!(cnjs, Cx | Dx)
    append!(cnjs, _handle_lemma4(Cx, Rxy, k2; vars, data))
    append!(cnjs, _handle_lemma4(Dx, Rxy, k2; vars, data))

    push!(data[:ccs], CC((Rx.operator, 1), k1))

    return cnjs
end

"""ϕ = V x ϕ(x) | E=k y ψ(x, y)"""
function _handle_lemma4(ϕ, ψ, k; vars, data)
    count_cnt = data[:counting]
    data[:counting] += 1

    K = parse_formula("K$count_cnt($(vars[1]), $(vars[2]))")
    L = parse_formula("L$count_cnt($(vars[2]))")

    cnjs = to_conjunctive_normal_form(Expression("==>", (ϕ & K), L)) |> conjuncts
    append!(cnjs, to_conjunctive_normal_form(Expression("==>", ~ϕ, Expression("<=>", ψ, K))) |> conjuncts)
    
    push!(data[:ccs], CC((L.operator, 1), k))

    data[:weights][(K.operator, 2)] = (1, 1)
    data[:weights][(L.operator, 1)] = (1, 1)

    push!(data[:denoms], BinomialDenomTemplate(k))

    append!(cnjs, _handle_forall_existsK(K, k; vars, data))

    return cnjs
end
