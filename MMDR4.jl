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

# Prendiamo un grafo bipartito avente n nodi a sinistra (agenti) e n nodi a destra (posizioni)

# Definisco le variabili che verranno usate nei metodi che implementano il Ford-Fulkerson Algorithm (flood, reverse, reset_flooding)
# variabile[1][i] corrisponde all'i-esimo nodo di sinistra; variabile[2][i] corrisponde all'i-esimo nodo di destra.

out = Vector{Vector{Vector{Int}}}(undef, 2)   # allowedEdge, contiene i path agenti-posizioni; aggiornato dalla Breadth-First Search

visited = Vector{Vector{Bool}}(undef, 2)      # curNode; Vettore visited, indica se un nodo è stato o meno visitato -> es.[[1,0,0],[0,1,0]] 1:si, 0:no 

back = Vector{Vector{Int}}(undef, 2)          # prevNode; indica come raggiungere un determinato nodo

used = Vector{Int}(undef, N)                  # matchingAgent, indica se uno dei nodi agente è stato usato o meno; 1:si, 0:no

cost_int = fill(-(N+1), (N, N))                   # Matrice dei costi (NxN)

#------------------------------------------------
# Algoritmo di Floodfill, partendo da un nodo.
# x:{1,2}. 1, nodo di sinistra; 2, nodo di destra
#  y:{1,...,n}. Indica il nodo che sto considerando
# prev:{-1, 1,..., n}. -1 indica un nodo non ancora assegnato. 
#                       1...n indicano il nodo considerato nel lato 3-x (se x = 1 -> destra, se x = 2 -> sinistra)

#Return: se ha raggiungo un nodo non ancora assegnato di destra, ritorna quel nodo. Altrimenti ritorna -1
function flood(x, y, prev)
    visited[x][y] = true
    back[x][y] = prev
    if x == 2 && isempty(out[x][y])  # Nodo non assegnato
        return y
    end
    
    for j in 1:length(out[x][y])
        if !visited[3 - x][out[x][y][j]]
            tmp = flood(3 - x, out[x][y][j], y)
            if tmp != -1  # L'algoritmo ha raggiunto la fine
                return tmp
            end
        end
    end
    return -1
end


#------------------------------------------------
#Partendo dal nodo corrispondente ad x ed y, ripercorre inversamente il grafo, attraverso back 

#Return: ritorna il nodo di sinistra non assegnato trovato
function reverse(x, y)
    
    while true
        prev = back[x][y]
        if prev == -1  # Nodo di sinistra non assegnato
            break
        end
        push!(out[x][y], prev)
        filter!((k)-> k!=y, out[3-x][prev] )
        
        x, y = 3 - x, prev #riassegno x ed y ed il ciclo riparte
    end
    
    return y
end

#------------------------------------------------
#vengono re-inizializzati i valori di visited ed il flood riparte dai nodi di sinistra
function reset_flooding(n)
    for i in 1:2
        fill!(visited[i], false)
    end

    for j in 1:n
        if used[j] == 0
            flood(1, j, -1)
        end
    end
end

#------------------------------------------------
#  Aggiunge archi Edge fino a che non ho k abbinamenti

#  Return: ritorna l'indice dell'ultimo nodo aggiunto
function getMinimalMaxEdgeInPerfectMatching(edges, n, k)
    #re-imposto il grafo
    for i in 1:2
        out[i] = Vector{Vector{Int}}(undef, n)
        for j in 1:n
            out[i][j] = Int[]
        end
    end
    fill!(used, 0)
    reset_flooding(n)

    answer = Ref(1)
    for answer[] in 1:length(edges)
        e = edges[answer[]].nodes
        push!(out[1][e[1]], e[2])
        #println(e[1], ",", e[2])

        if visited[1][e[1]] && !visited[2][e[2]]
            ans = flood(2, e[2], e[1])
            if ans != -1  # se flood ritorna un nodo non ancora assegnato
                k -= 1 #decremento k e continuo il for fino a che k == 0
                if k == 0
                    break
                end
                start = reverse(2, ans)
                used[start] = 1
                reset_flooding(n)
            end
        end
    end
    return answer[]
end
#FINE MIO

#Hungarian alg. O(n^3) from https://www.topcoder.com/thrive/articles/Assignment%20Problem%20and%20Hungarian%20Algorithm 
const INF = typemax(Float64)  # just infinity

const n_int = Ref{Int}(0)
const max_match_int = Ref{Int}(0)  # n workers and n jobs

lx_int = zeros(Int64, N)  # labels of X and Y parts
ly_int = zeros(Int64, N)
xy_int = fill(-1, N)  # xy[x] - vertex that is matched with x
yx_int = fill(-1, N)  # yx[y] - vertex that is matched with y
S_int = falses(N)  # sets S and T in algorithm
T_int = falses(N)
slack_int = fill(0, N)  # as in the algorithm description
slackx_int = fill(0, N)   # slackx[y] such a vertex, that ...
prev_int = fill(0, N)     # array for memorizing alternating paths

function init_labels_int()
    fill!(lx_int, 0)
    fill!(ly_int, 0)
    for x in 1:n_int[]
        for y in 1:n_int[]
            lx_int[x] = max(lx_int[x], cost_int[x, y])
        end
    end
end

function update_labels_int()
    delta = typemax(Int)  # init delta as infinity
    y = Ref(1)
    x = Ref(1)
    for y[] in 1:n_int[]
        if !T_int[y[]]
            delta = min(delta, slack_int[y[]])
        end
    end
    for x[] in 1:n_int[]
        if S_int[x[]]
            lx_int[x[]] -= delta
        end
    end
    for y[] in 1:n_int[]
        if T_int[y[]]
            ly_int[y[]] += delta
        end
    end
    for y[] in 1:n_int[]
        if !T_int[y[]]
            slack_int[y[]] -= delta
        end
    end
end

function add_to_tree_int(x, prevx)
    S_int[x] = true
    prev_int[x] = prevx
    for y in 1:n_int[]
        if lx_int[x] + ly_int[y] - cost_int[x, y] < slack_int[y]
            #println("test1: ", lx_int[x]) 
            #println("test2: ", ly_int[y]) 
            #println("test3: ", cost_int[x, y]) 
            #println("test4: ", slack_int[y]) 
            slack_int[y] = lx_int[x] + ly_int[y] - cost_int[x, y] #1
            slackx_int[y] = x #1
            
        end
    end
end

function augment_int()
    if max_match_int[] == n_int[]
        return true
    end
    
    q = zeros(Int, N)
    wr = Ref(1)
    rd = Ref(1)
    fill!(S_int, false)
    fill!(T_int, false)
    fill!(prev_int, -1)
    x = Ref(1)
    y = Ref(1)
    root = 1

    for x[] in 1:n_int[]
        if xy_int[x[]] == -1

            q[wr[]] = root = x[]
            wr[] = wr[] + 1
            prev_int[x[]] = -2
            S_int[x[]] = true
            break
        end
    end


    for y[] in 1:n_int[]
        slack_int[y[]] = lx_int[root] + ly_int[y[]] - cost_int[root, y[]]
        slackx_int[y[]] = root
    end

    
    while true
        while rd[] < wr[]
            x[] = q[rd[]]
            rd[] = rd[] + 1
            for y[] in 1:n_int[]
                if cost_int[x[], y[]] == lx_int[x[]] + ly_int[y[]] && !T_int[y[]]

                    if yx_int[y[]] == -1
                        break
                    end
                    T_int[y[]] = true
                    q[wr[]] = yx_int[y[]]
                    wr[] = wr[] + 1
                    
                    
                    add_to_tree_int(yx_int[y[]], x[])
                    
                    if y[] == n_int[]
                        y[]+=1
                    end

                else
                    y[]+=1
                end
                if y[] > n_int[]
                    break
                end
            end
            
            if y[] <= n_int[]
                break
            end
        end
        if y[] <= n_int[]
            break
        end


        update_labels_int()
        wr[] = 1
        rd[] = 1
        for y[] in 1:n_int[]
            if !T_int[y[]] && slack_int[y[]] == 0
                if yx_int[y[]] == -1
                    x[] = slackx_int[y[]]
                    break
                else
                    T_int[y[]] = true
                    if !S_int[yx_int[y[]]]
                        q[wr[]] = yx_int[y[]]
                        wr[] = wr[] + 1
                        add_to_tree_int(yx_int[y[]], slackx_int[y[]])
                    end
                end
            end
        end
        if y[] <= n_int[]
            break
        end
    end
    if y[] <= n_int[]
        max_match_int[] += 1
        cx = x[]
        cy = y[]
        ty = Ref(0)

        while cx != -2

            ty[] = xy_int[cx]
            yx_int[cy] = cx
            xy_int[cx] = cy

            cy = ty[]
            cx = prev_int[cx]
        end
        return false
    end
    return true
end

function hungarian_int()
    ret = 0
    n_int[] = N
    max_match_int[] = 0
    fill!(xy_int, -1)
    fill!(yx_int, -1)

    init_labels_int()
    while !augment_int()

    end
    for x in 1:n_int[]
        ret += cost_int[x, xy_int[x]]
    end
    
    return ret
end
#End of Hungarian alg.

#MMDR O(n^4) implementation
function mmdr4(t::Test)

    n = length(t.starts)

    edges = Edge[]
    edges_tmp = Edge[]
    answer = Edge[]

    for i in 1:n
        for j in 1:n
            push!(edges, Edge( (hypot( t.starts[i].x - t.targets[j].x , t.starts[i].y - t.targets[j].y)) , (i, j)))
        end
    end

    for i in 1:2
        visited[i] = Vector{Bool}(undef, n)
        back[i] = Vector{Int}(undef, n)
    end

    k = n

    while k>0
        sort!(edges, by=x->x.dist)

        choice = getMinimalMaxEdgeInPerfectMatching(edges, n, n)
        max_edge_value = edges[choice].dist
        
        for i in 1:length(edges)
            if edges[i].dist < max_edge_value
                cost_int[edges[i].nodes[1], edges[i].nodes[2]] = 0
            elseif edges[i].dist == max_edge_value
                cost_int[edges[i].nodes[1], edges[i].nodes[2]] = -1
            else
                cost_int[edges[i].nodes[1], edges[i].nodes[2]] = -(n+1)
            end
        end
        
        l = -hungarian_int()
        k = k-l
        if k == 0
            break #fine
        end
       
        empty!(edges_tmp)
        for i in 1:length(edges)
            e = edges[i]
            if lx_int[e.nodes[1]] + ly_int[e.nodes[2]] == cost_int[e.nodes[1], e.nodes[2]]
                if e.dist == max_edge_value
                    e.dist = -1
                end
                push!(edges_tmp, e)
            else
                cost_int[e.nodes[1], e.nodes[2]] = -(n+1)
            end
        end
        empty!(edges)
        for edge_tmp in edges_tmp
            push!(edges, edge_tmp)
        end
    end

    for i in 1:n
        push!(answer, Edge( hypot( t.starts[i].x - t.targets[xy_int[i]].x , t.starts[i].y - t.targets[xy_int[i]].y) , (i, xy_int[i])))
    end

    return answer
end


# Main
function main()
    println("Numero di ripetizioni:", REPETITIONS)

    inizio = now()
    for iter in 1:REPETITIONS

        t = Test(Point[], Point[])

        for i in 1:N
            push!(t.starts, Point(rand() * (N * N) + 1, rand() * (N * N) + 1))
        end
        for i in 1:N
            push!(t.targets, Point(rand() * (N * N) + 1, rand() * (N * N) + 1))
        end

        result = mmdr4(t)

    end
    fine = now()
    println("Finito in ", fine-inizio)

end

main()