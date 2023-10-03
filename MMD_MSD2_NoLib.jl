using LinearAlgebra 
using Distances
using Dates

#OK!!

const REPETITIONS = 10 #Numero di ripetizioni fatte
const N = 1000#Numero di nodi per lato

#Definisco un punto come una coppia di valori x e y
struct Point 
    x::Float64
    y::Float64
end

# Il generico arco Edge avrà una forma del tipo (dist, (left node, right node))
struct Edge
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

used = fill(0, N)                             # matchingAgent, indica se uno dei nodi agente è stato usato o meno; 1:si, 0:no

cost = zeros(Float64, N, N)                   # Matrice dei costi (NxN)

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

#HUNGARIAN
const INF = typemax(Float64)  # just infinity

const n = Ref{Int}(N)
const max_match = Ref{Int}(0)  # n workers and n jobs


lx = zeros(Float64, N)  # labels of X and Y parts
ly = zeros(Float64, N)
xy = fill(-1, N)  # xy[x] - vertex that is matched with x
yx = fill(-1, N)  # yx[y] - vertex that is matched with y
S = falses(N)  # sets S and T in algorithm
T = falses(N)
slack = zeros(Float64, N)  # as in the algorithm description
slackx = zeros(Int64, N)   # slackx[y] such a vertex, that ...
prev = zeros(Int64, N)     # array for memorizing alternating paths


function init_labels()

    for x in 1:n[]
        for y in 1:n[]
            lx[x] = max(lx[x], cost[x, y])
        end
    end

end

function update_labels()

    x = Ref(1)
    y = Ref(1)

    delta = Ref(INF)

    for y[] in 1:n[]
        if !T[y[]]
            delta[] = min(delta[], slack[y[]])
        end
    end

    for x[] in 1:n[]
        if S[x[]]
            lx[x[]] -= delta[]
        end
    end

    for y[] in 1:n[]
        if T[y[]]
            ly[y[]] += delta[]
        end
    end

    for y[] in 1:n[]
        if !T[y[]]
            slack[y[]] -= delta[]
        end
    end

end

function add_to_tree(x, prevx)

    S[x] = true
    prev[x] = prevx
    
    for y in 1:n[]
        if lx[x] + ly[y] - cost[x, y] < slack[y]

            slack[y] = lx[x] + ly[y] - cost[x, y]
            slackx[y] = x

        end
    end

end

function augment()

    if max_match[] == n[]
        return true
    end

    x = Ref(1)
    y = Ref(1)
    root = 1

    q = zeros(Int64, N)
    wr = Ref(1)
    rd = Ref(1)

    fill!(S, false)
    fill!(T, false)
    fill!(prev, -1)

    for x[] in 1:n[]
        if xy[x[]] == -1

            q[wr[]] = root = x[]
            wr[] = wr[] + 1
            prev[x[]] = -2
            S[x[]] = true

            break
        end
    end

    for y[] in 1:n[]
        slack[y[]] = lx[root] + ly[y[]] - cost[root, y[]]
        slackx[y[]] = root
    end

    while true
        while rd[] < wr[]

            x[] = q[rd[]]
            rd[]+=1

            for y[] in 1:n[]
                if cost[x[], y[]] == lx[x[]] + ly[y[]] && !T[y[]]

                    if yx[y[]] == -1
                        break
                    end

                    T[y[]] = true
                    q[wr[]] = yx[y[]]
                    wr[]+=1

                    add_to_tree(yx[y[]], x[])
                
                    if y[] == n[]
                        y[]+=1
                    end

                else
                    y[]+=1
                end
                if y[] > n[]
                    break
                end
            end
            
            if y[] <= n[]
                break
            end
        end

        if y[] <= n[]
            break
        end

        update_labels()

        wr[] = 1
        rd[] = 1

        for y[] in 1:n[]

            if !T[y[]] && slack[y[]] == 0
                if yx[y[]] == -1

                    x = slackx[y[]]
                    break

                else

                    T[y[]] = true
                    if !S[yx[y[]]]

                        q[wr[]] = yx[y[]]
                        wr[]+=1

                        add_to_tree(yx[y[]], slackx[y[]])

                    end
                end
            end
        end

        if y[] < n[]
            break
        end
    end

    if y[] <= n[]
        max_match[] += 1
        cx = x[]
        cy = y[]
        ty = Ref(0)

        while cx != -2
            ty[] = xy[cx]
            yx[cy] = cx
            xy[cx] = cy

            cy = ty[]
            cx = prev[cx]
        end
        return false
    end
    return true

end

function hungarian()

    for i in 1:N
        for j in 1:N
            cost[i, j] *= -1
        end
    end

    init_labels()

    while !augment()

    end

end


# Algoritmo MMD_MSD2
function mmd_msd2(t::Test)

    n = length(t.starts) #uguale a lenght(t.targets)
    # Viene inizializzato un vettore vuoto edges dove inserire gli archi Edge.
    edges = Edge[]
    answer = Edge[]

    # Inserisco gli Edge in edges
    for i in 1:n
        for j in 1:n
            push!(edges, Edge( (hypot( t.starts[i].x - t.targets[j].x , t.starts[i].y - t.targets[j].y))^2 , (i, j)))
        end
    end
    # ordino gli archi di edges in ordine crescente di distanza
    sort!(edges, by=x->x.dist)

    # Imposto le dimensioni dei vettori utilizzati
    for i in 1:2
        visited[i] = Vector{Bool}(undef, n)
        back[i] = Vector{Int}(undef, n)
    end

    # Richiamo getMinimalMaxEdgeInPerfectMatching per ottenere il minimo arco massimo
    # choice sarà l'indice da utilizzare nel vettore edges per ottenere l'arco desiderato
    choice = getMinimalMaxEdgeInPerfectMatching(edges, n, n)
    max_edge_value = edges[choice].dist
    
    # costruisco la matrice dei costi
    for i in 1:length(edges)
        if edges[i].dist <= max_edge_value
            cost[edges[i].nodes[1], edges[i].nodes[2]] = edges[i].dist
        else
            cost[edges[i].nodes[1], edges[i].nodes[2]] = max_edge_value * n + 1
        end
    end
    # utilizzo l'Hungarian Algorithm per ottenere l'assegnamento desiderato
    hungarian()

    for i in 1:n
        push!( answer , Edge( hypot( t.starts[i].x - t.targets[xy[i]].x , t.starts[i].y - t.targets[xy[i]].y) , (i, xy[i]) ) )
    end

    return answer
end

# Main
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

        result = mmd_msd2(t)

    end
    fine = now()
    println("Finito in ", fine-inizio)
    #Avg. time in: Ryzen 7 3700U @ 2.3 GHz (10 ripetizioni)
    # N = 10 -> 358 millisecondi
    # N = 100 -> 1888 millisecondi
    # N = 300 -> 
    # N = 500 -> 
    # N = 1000 -> 
    # N = 10000 -> 
end

main()
