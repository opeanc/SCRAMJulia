using Dates

const REPETITIONS = 10 #Numero di ripetizioni fatte
const N = 10 #Numero di nodi per lato

#Definisco un punto come una coppia di valori x e y
struct Point 
    x::Float64
    y::Float64
end

# Il generico arco Edge avrà una forma del tipo (dist, (left node, right node))
mutable struct Edge
    dist::Float64
    nodes::Tuple{Int, Int}
end

#La struct Test è composta da punti starts (gli agenti) e targets(posizioni-obiettivo)
struct Test
    starts::Vector{Point}
    targets::Vector{Point}
end

newdist = zeros(Int64, N, N)

const DATA_64WORDS_SIZE = div(N*N-1, 64)+2 #uso la funzione div per ottenere un intero

const n_large = Ref{Int64}(N)
const max_match_large = Ref{Int64}(0)  # n workers and n jobs

lx_large = zeros(UInt64, N, DATA_64WORDS_SIZE)  # labels of X and Y parts
ly_large = zeros(UInt64, N, DATA_64WORDS_SIZE)
xy_large = fill(-1, N)
yx_large = fill(-1, N)
  # yx[y] - vertex that is matched with y
S_large = falses(N)  # sets S and T in algorithm
T_large = falses(N)
slack_large = zeros(UInt64, N, DATA_64WORDS_SIZE)  # as in the algorithm description
slackx_large = fill(0, N)   # slackx[y] such a vertex, that ...
prev_large = fill(0, N)     # array for memorizing alternating paths

#Operations for 64 bit values
function set_zero(value::Vector{UInt64})

    value[DATA_64WORDS_SIZE] = 0

    for i in 1:DATA_64WORDS_SIZE-1
        value[i] = 0
    end

    return value
    
end


function set_bit(value::Vector{UInt64}, bit::Int64)
    value = set_zero(value)
    
    val = UInt64(1) << (abs(bit) % 64)
    if val != 1
        val = div(val, 2)
    end
    value[DATA_64WORDS_SIZE - div( abs(bit) , 64 ) - 1] = val
    if bit < 0
        value[DATA_64WORDS_SIZE] = 1
    end    
end

function is_less_than(valueA::Vector{UInt64}, valueB::Vector{UInt64})

    negA = valueA[DATA_64WORDS_SIZE]
    negB = valueB[DATA_64WORDS_SIZE]

    if negA == 0 && negB == 1
        return false
    elseif negA == 1 && negB == 0
        return true
    end

    for i in 1:DATA_64WORDS_SIZE
        if valueA[i] == valueB[i]
            continue
        end
        return (valueA[i] < valueB[i]) ⊻ negA == 1
    end
    return false

end

function assign_value(valueA::Vector{UInt64}, valueB::Vector{UInt64})
    for i in 1:DATA_64WORDS_SIZE
        valueA[i] = valueB[i]
    end

    return valueA
end

function is_zero(value::Vector{UInt64})

    for i in 1:DATA_64WORDS_SIZE
        if value[i] != 0
            return false
        end
    end
    
    return true
end

function is_equal(valueA::Vector{UInt64}, valueB::Vector{UInt64})

    if valueA[DATA_64WORDS_SIZE] != valueB[DATA_64WORDS_SIZE]
        
        if is_zero(valueA) && is_zero(valueB)
            return true
        end
        return false
    end

    for i in 1:DATA_64WORDS_SIZE
        if valueA[i] != valueB[i]
            return false
        end
    end

    return true
end

function subtract_value(valueA::Vector{UInt64}, valueB::Vector{UInt64})
    
    if is_equal(valueA, valueB)
        valueA = set_zero(valueA)
        return valueA
    end
    negA = valueA[DATA_64WORDS_SIZE]
    negB = valueB[DATA_64WORDS_SIZE]

    if negA != negB
        temp = zeros(UInt64, DATA_64WORDS_SIZE)

        temp = assign_value(temp, valueB)

        if temp[DATA_64WORDS_SIZE] == 0
            temp[DATA_64WORDS_SIZE] = 1
        elseif temp[DATA_64WORDS_SIZE] == 1
            temp[DATA_64WORDS_SIZE] = 0
        end

        valueA = add_value(valueA, temp)
        
        return valueA

    end

    if (negA == 0 && is_less_than(valueA, valueB)) || (negA == 1 && is_less_than(valueB, valueA))
        
        temp = zeros(UInt64, DATA_64WORDS_SIZE)

        temp = assign_value(temp, valueB)

        temp = subtract_value(temp, valueA)

        if temp[DATA_64WORDS_SIZE] == 0
            temp[DATA_64WORDS_SIZE] = 1
        elseif temp[DATA_64WORDS_SIZE] == 1
            temp[DATA_64WORDS_SIZE] = 0
        end

        valueA = assign_value(valueA, temp)

        return valueA

    end

    negValueB = zeros(UInt64, DATA_64WORDS_SIZE)

    for i in 1:DATA_64WORDS_SIZE-1
        negValueB[i] = ~valueB[i] 
    end
    negValueB[DATA_64WORDS_SIZE] = 0

    one = zeros(UInt64, DATA_64WORDS_SIZE)
    set_bit(one, 0)

    one[DATA_64WORDS_SIZE] = 0
    
    negValueB = add_value(negValueB, one)
    #println("negValueB dopo 1: ",negValueB[1])
    #println("negValueB dopo 2: ",negValueB[2])

    signA = valueA[DATA_64WORDS_SIZE]

    valueA[DATA_64WORDS_SIZE] = 0
    valueA = add_value(valueA, negValueB)
    valueA[DATA_64WORDS_SIZE] = signA

    return valueA

end

function add_value(valueA::Vector{UInt64}, valueB::Vector{UInt64})

    if valueA[DATA_64WORDS_SIZE] != valueB[DATA_64WORDS_SIZE]
        temp = zeros(UInt64, DATA_64WORDS_SIZE)
        temp = assign_value(temp, valueB)

        if temp[DATA_64WORDS_SIZE] == 0
            temp[DATA_64WORDS_SIZE] = 1
        elseif temp[DATA_64WORDS_SIZE] == 1
            temp[DATA_64WORDS_SIZE] = 0
        end

        valueA = subtract_value(valueA, temp)
        return valueA
    end
    
    carry = 0
    i = DATA_64WORDS_SIZE-1
    
    while i > 0

        valueA[i] = valueA[i] + valueB[i] + carry

        overflow = false
        if valueA[i] == valueB[i] && carry == 1
            overflow = true
        end

        if valueA[i] < valueB[i] || overflow
            carry = 1
        else
            carry = 0
        end

        i = i-1

    end

    return valueA

end

function set_max(value::Vector{UInt64})

    value[DATA_64WORDS_SIZE] = 0 

    max_int = typemax(UInt64)

    for i in 1:DATA_64WORDS_SIZE-1
        value[i] = max_int
    end

end

#End of operation for 64 bit values

#Hungarian alg. O(n^3) from https://www.topcoder.com/thrive/articles/Assignment%20Problem%20and%20Hungarian%20Algorithm 
function init_labels_large()

    for x in 1:n_large[]
        for y in 1:n_large[]
            cost = zeros(UInt64, DATA_64WORDS_SIZE)
            set_bit(cost, newdist[x, y])
            if is_less_than(lx_large[x, :], cost)
                lx_large[x, :] = assign_value(lx_large[x, :], cost)
            end
        end
    end

end

function update_labels_large()
    
    x = Ref(1)
    y = Ref(1)
    
    delta = zeros(UInt64, DATA_64WORDS_SIZE)
    
    set_max(delta)

    for y[] in 1:n_large[]
        if !T_large[y[]]
            if is_less_than(slack_large[y[], :], delta)
                delta = assign_value(delta, slack_large[y[], :])
            end
        end
    end

    for x[] in 1:n_large[]
        if S_large[x[]]
            lx_large[x[], :] = subtract_value(lx_large[x[], :], delta)
        end
    end

    for y[] in 1:n_large[]
        if T_large[y[]]
            ly_large[y[], :] = add_value(ly_large[y[], :], delta)
        end
    end

    for y[] in 1:n_large[]
        if !T_large[y[]]
            slack_large[y[], :] = subtract_value(slack_large[y[], :], delta)
        end
    end

end

function add_to_tree_large(x, prevx)

    S_large[x] = true
    prev_large[x] = prevx
    
    for y in 1:n_large[]

        temp = zeros(UInt64, DATA_64WORDS_SIZE)

        temp = assign_value(temp, lx_large[x, :])
        temp = add_value(temp, ly_large[y, :])

        cost = zeros(UInt64, DATA_64WORDS_SIZE)
        set_bit(cost, newdist[x, y])
        
        temp = subtract_value(temp, cost)
        
        if is_less_than(temp, slack_large[y, :])
            slack_large[y, :] = assign_value(slack_large[y, :], temp)
            slackx_large[y] = x
        end
    end

end

function augment_large()

    if max_match_large[] == n_large[]
        return true
    end
    
    q = zeros(Int, N)
    wr = Ref(1)
    rd = Ref(1)
    fill!(S_large, false)
    fill!(T_large, false)
    fill!(prev_large, -1)
    x = Ref(1)
    y = Ref(1)
    root = 1

    for x[] in 1:n_large[]
        if xy_large[x[]] == -1

            q[wr[]] = root = x[]
            wr[] = wr[] + 1
            prev_large[x[]] = -2
            S_large[x[]] = true
            break
        end
    end

    for y[] in 1:n_large[]
        
        slack_large[y[], :] = assign_value(slack_large[y[], :], lx_large[root, :])
        slack_large[y[], :] = add_value(slack_large[y[], :], ly_large[y[], :])

        cost = zeros(UInt64, DATA_64WORDS_SIZE)
        set_bit(cost, newdist[root, y[]])
        slack_large[y[], :] = subtract_value(slack_large[y[], :], cost)

        slackx_large[y[]] = root

    end

    while true
        while rd[] < wr[]
            x[] = q[rd[]]
            rd[] = rd[] + 1

            for y[] in 1:n_large[]
                temp = zeros(UInt64, DATA_64WORDS_SIZE)
                temp = assign_value(temp, lx_large[x[], :])
                temp = add_value(temp, ly_large[y[], :])

                cost = zeros(UInt64, DATA_64WORDS_SIZE)
                set_bit(cost, newdist[x[], y[]])

                if is_equal(cost, temp) && !T_large[y[]]
                    if yx_large[y[]] == -1
                        break
                    end

                    T_large[y[]] = true
                    q[wr[]] = yx_large[y[]]
                    wr[] = wr[] + 1

                    add_to_tree_large(yx_large[y[]], x[])
                    if y[] == n_large[]
                        y[]+=1
                    end
                
                else
                    y[]+=1
                end

                if y[] > n_large[]
                    break
                end
            end

            if y[] <= n_large[]
                break
            end
        end

        if y[] <= n_large[]
            break
        end
        update_labels_large()

        wr[] = 1
        rd[] = 1

        for y[] in 1:n_large[]

            if !T_large[y[]] && is_zero(slack_large[y[], :])

                if yx_large[y[]] == -1
                    x[] = slackx_large[y[]]
                    break
                else
                    T_large[y[]] = true
                    if !S_large[yx_large[y[]]]
                        q[wr[]] = yx_large[y[]]
                        wr[] = wr[] + 1
                        add_to_tree_large(yx_large[y[]], slackx_large[y[]])
                    end
                end
            end
        end
        if y[] < n_large[]
            break
        end
    end
    if y[] <= n_large[]
        max_match_large[] += 1
        cx = x[]
        cy = y[]
        ty = Ref(0)

        while cx != -2

            ty[] = xy_large[cx]
            yx_large[cy] = cx
            xy_large[cx] = cy

            cy = ty[]
            cx = prev_large[cx]
        end
        return false
    end
    return true

end


function hungarian()

    init_labels_large()

    while !augment_large()
    end

end
#End of Hungarian alg.

#MMDR O(n^5) implementation
function mmdr5(t::Test)

    n = length(t.starts)

    edges = Edge[]
    answer = Edge[]

    # Inserisco gli Edge in edges
    for i in 1:n
        for j in 1:n
            push!(edges, Edge( hypot( t.starts[i].x - t.targets[j].x , t.starts[i].y - t.targets[j].y) , (i, j)))
        end
    end
    # ordino gli archi di edges in ordine crescente di distanza
    sort!(edges, by=x->x.dist)

    lasti = -1
    newdist[edges[1].nodes[1], edges[1].nodes[2]] = -lasti
    for i in 2:length(edges)
        if i== 2
            lasti = i
        elseif i > 2 || edges[i].dist != edges[lasti].dist
            lasti = i
        end
        newdist[edges[i].nodes[1], edges[i].nodes[2]] = -lasti
    end

    hungarian()
    
    for i in 1:n
        push!( answer , Edge( hypot( t.starts[i].x - t.targets[xy_large[i]].x , t.starts[i].y - t.targets[xy_large[i]].y) , (i, xy_large[i]) ) )
    end


    return answer
end

function main()

    println("Numero di ripetizioni: ", REPETITIONS)

    inizio = now()
    for iter in 1:REPETITIONS

        t = Test(Point[], Point[])

        for i in 1:N
            push!(t.starts, Point(rand() * (N * N) + 1, rand() * (N * N) + 1))
        end
        for i in 1:N
            push!(t.targets, Point(rand() * (N * N) + 1, rand() * (N * N) + 1))
        end

        mmdr5(t)

    end
    fine = now()
    println("Finito in ", fine-inizio)
end

main()