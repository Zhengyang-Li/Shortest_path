using DataStructures

# Define the Link struct to represent bi-attribute links
mutable struct Link
    tail::Int           # Starting node of the link
    head::Int           # Ending node of the link
    time::Float64       # Time cost of the link
    toll::Float64       # Toll cost of the link
    cost::Float64       # Generalized cost (updated during algorithm)
end

# Define the Node struct to represent network nodes
struct Node
    Id::Int                          # Node identifier
    outLinks::Vector{Tuple{Int, Int}} # Outgoing links as (tail, head) tuples
    inLinks::Vector{Tuple{Int, Int}}  # Incoming links as (tail, head) tuples
end

# Define a TransportationNetwork struct to hold the network
struct TransportationNetwork
    node::Dict{Int, Node}             # Dictionary of nodes
    link::Dict{Tuple{Int, Int}, Link} # Dictionary of links
end

# Customized Dijkstra's algorithm for the parametric bi-objective problem
function _Dijkstra(nodeSet::Dict{Int, Node}, linkSet::Dict{Tuple{Int, Int}, Link}, ori::Int)
    path = Dict(ori => [ori])          # Paths to nodes
    pred = Dict{Int, Int}(ori => nothing)        # Predecessors ('NA' in Python becomes nothing)
    dist = Dict{Int, Float64}()        # Permanent labels
    time = Dict(ori => 0.0)            # Cumulative time
    toll = Dict(ori => 0.0)            # Cumulative toll
    TL = Dict{Int, Float64}()          # Temporary labels
    SE = MutableBinaryMinHeap{Tuple{Float64, Float64, Float64, Int}}() # Scan eligible list
    push!(SE, (0.0, 0.0, 0.0, ori))    # Initial entry: (label, time, toll, node)

    while !isempty(SE)
        u_label, u_time, u_toll, u = pop!(SE)
        if haskey(dist, u)
            continue  # Skip if node is already permanently labeled
        end
        dist[u] = u_label
        time[u] = u_time
        toll[u] = u_toll
        for l in nodeSet[u].outLinks
            v = l[2]  # Head of the link
            v_new_label = dist[u] + linkSet[l].cost
            v_new_time = time[u] + linkSet[l].time
            v_new_toll = toll[u] + linkSet[l].toll
            if haskey(dist, v)
                continue  # Skip if v is already processed
            elseif !haskey(TL, v) || v_new_label < TL[v]
                TL[v] = v_new_label
                push!(SE, (v_new_label, v_new_time, v_new_toll, v))
                path[v] = [path[u]..., v]  # Extend path by appending v
                pred[v] = u
            end
        end
    end

    return path, pred, time, toll
end

# Main bi-objective shortest path algorithm
function BiObj_Dijkstra_ESNP(TN::TransportationNetwork, ori::Int, TEM_LB::Float64, TEM_UB::Float64)
    """
    Parametric bi-objective shortest path algorithm to generate all extreme supported
    non-dominated paths using a Dijkstra-like method.

    Args:
        TN: TransportationNetwork containing node and link sets
        ori: Origin node ID (integer)
        TEM_LB: Lower bound of time equivalence of money (TEM)
        TEM_UB: Upper bound of TEM

    Returns:
        path_dict: Dict of paths (Vector of Vectors) keyed by destination node
        dist_dict: Dict of costs (Vector of (time, toll) tuples) keyed by destination node
        bound_dict: Dict of TEM boundaries (Vector) keyed by destination node
    """
    nodeSet = TN.node
    linkSet = TN.link

    # Dictionaries to store results
    path_dict = Dict{Int, Vector{Vector{Int}}}()
    dist_dict = Dict{Int, Vector{Tuple{Float64, Float64}}}()
    bound_dict = Dict{Int, Vector{Float64}}()

    # Initialize labels for all nodes
    ratio = Dict(n => Inf for n in keys(nodeSet))        # Minimum ratio for tree change
    c2_hat = Dict(n => Inf for n in keys(nodeSet))       # Reduced toll for tie-breaking
    last_ratio = Dict(n => 0.0 for n in keys(nodeSet))   # Last ratio used
    Lpred = Dict(n => nothing for n in keys(nodeSet))    # Latent predecessor
    time_tree = Dict(n => Inf for n in keys(nodeSet))    # Time on current tree
    toll_tree = Dict(n => Inf for n in keys(nodeSet))    # Toll on current tree
    reduce_time = Dict(l => Inf for l in keys(linkSet))  # Reduced time for links
    reduce_toll = Dict(l => Inf for l in keys(linkSet))  # Reduced toll for links

    # Set initial generalized costs
    for l in keys(linkSet)
        linkSet[l].cost = linkSet[l].time + TEM_LB * linkSet[l].toll
    end

    # Compute initial shortest path tree
    path_tree, pred, init_time_tree, init_toll_tree = _Dijkstra(nodeSet, linkSet, ori)

    # Update tree and record initial paths
    for n in keys(path_tree)
        time_tree[n] = init_time_tree[n]
        toll_tree[n] = init_toll_tree[n]
        path_dict[n] = [path_tree[n]]
        dist_dict[n] = [(time_tree[n], toll_tree[n])]
        bound_dict[n] = [TEM_LB]
    end

    # Compute initial reduced costs
    for j in keys(path_tree)
        for (i, j) in nodeSet[j].inLinks
            if haskey(time_tree, i)  # Ensure predecessor is reachable
                reduce_time[(i, j)] = time_tree[i] + linkSet[(i, j)].time - time_tree[j]
                reduce_toll[(i, j)] = toll_tree[i] + linkSet[(i, j)].toll - toll_tree[j]
                if reduce_toll[(i, j)] < 0
                    tmp_ratio = -reduce_time[(i, j)] / reduce_toll[(i, j)]
                    if (tmp_ratio, reduce_toll[(i, j)]) < (ratio[j], c2_hat[j])
                        ratio[j] = tmp_ratio
                        c2_hat[j] = reduce_toll[(i, j)]
                        Lpred[j] = i
                    end
                end
            end
        end
    end

    # Initialize scan eligible list with nodes having latent predecessors
    SE = MutableBinaryMinHeap{Tuple{Tuple{Float64, Float64}, Int}}()
    for n in keys(path_tree)
        if Lpred[n] !== nothing
            push!(SE, ((ratio[n], c2_hat[n]), n))
        end
    end

    # Main loop to find all extreme supported non-dominated paths
    while !isempty(SE)
        (j_ratio, j_reduce_toll), j = pop!(SE)
        if j_ratio >= TEM_UB
            continue
        end
        i = Lpred[j]
        time_tree[j] = time_tree[i] + linkSet[(i, j)].time
        toll_tree[j] = toll_tree[i] + linkSet[(i, j)].toll
        if j_ratio > last_ratio[j]
            pred[j] = i
            new_path = [path_dict[i][end]..., j]  # Create path on the fly
            push!(path_dict[j], new_path)
            push!(dist_dict[j], (time_tree[j], toll_tree[j]))
            push!(bound_dict[j], j_ratio)
        end
        last_ratio[j] = j_ratio
        ratio[j] = Inf
        Lpred[j] = nothing

        # Scan incoming links to update latent predecessor
        for (i, j) in nodeSet[j].inLinks
            if haskey(time_tree, i)
                reduce_time[(i, j)] = time_tree[i] + linkSet[(i, j)].time - time_tree[j]
                reduce_toll[(i, j)] = toll_tree[i] + linkSet[(i, j)].toll - toll_tree[j]
                if reduce_toll[(i, j)] < 0
                    tmp_ratio = -reduce_time[(i, j)] / reduce_toll[(i, j)]
                    if (tmp_ratio, reduce_toll[(i, j)]) < (ratio[j], c2_hat[j])
                        ratio[j] = tmp_ratio
                        c2_hat[j] = reduce_toll[(i, j)]
                        Lpred[j] = i
                    end
                end
            end
        end

        if Lpred[j] !== nothing
            push!(SE, ((ratio[j], c2_hat[j]), j))
        end

        # Scan outgoing links to update downstream nodes
        for (j, k) in nodeSet[j].outLinks
            if haskey(time_tree, k)
                reduce_time[(j, k)] = time_tree[j] + linkSet[(j, k)].time - time_tree[k]
                reduce_toll[(j, k)] = toll_tree[j] + linkSet[(j, k)].toll - toll_tree[k]
                if reduce_toll[(j, k)] < 0
                    tmp_ratio = -reduce_time[(j, k)] / reduce_toll[(j, k)]
                    if (tmp_ratio, reduce_toll[(j, k)]) < (ratio[k], c2_hat[k])
                        ratio[k] = tmp_ratio
                        c2_hat[k] = reduce_toll[(j, k)]
                        Lpred[k] = j
                        push!(SE, ((tmp_ratio, reduce_toll[(j, k)]), k))  # Add new entry
                    end
                end
            end
        end
    end

    # Add upper bound to all boundary lists
    for n in keys(bound_dict)
        push!(bound_dict[n], TEM_UB)
    end

    return path_dict, dist_dict, bound_dict
end

# Example usage
# tail, head, cost
linkData = [
    [1, 2, 10.0, 4.0],
    [1, 3, 6.0, 1.0],
    [2, 4, 0.0, 10.0],
    [3, 2, 6.0, 2.0],
    [3, 5, 1.0, 4.0],
    [4, 3, 4.0, 0.0],
    [4, 6, 10.0, 1.0],
    [5, 4, 5.0, 1.0],
    [5, 6, 6.0, 0.0],
]

# Create the transportation network
function create_network(linkData)
    nodeSet = Dict{Int, Node}()
    linkSet = Dict{Tuple{Int, Int}, Link}()

    for data in linkData
        tail, head, time, toll = data
        if !haskey(nodeSet, tail)
            nodeSet[tail] = Node(tail, [], [])
        end
        if !haskey(nodeSet, head)
            nodeSet[head] = Node(head, [], [])
        end
        linkKey = (tail, head)
        linkSet[linkKey] = Link(tail, head, time, toll, time + 0.1 * toll)  # Initial cost
        push!(nodeSet[tail].outLinks, (tail, head))
        push!(nodeSet[head].inLinks, (tail, head))
    end

    return TransportationNetwork(nodeSet, linkSet)
end

network = create_network(linkData)

# Run the bi-objective Dijkstra algorithm
ori = 1
TEM_LB = 0.0
TEM_UB = 10.0
path_dict, dist_dict, bound_dict = BiObj_Dijkstra_ESNP(network, ori, TEM_LB, TEM_UB)
# Print results
for (dest, paths) in path_dict
    println("Paths to node $dest:")
    for path in paths
        println("  Path: ", path)
    end
end
for (dest, costs) in dist_dict
    println("Costs to node $dest:")
    for cost in costs
        println("  Cost: ", cost)
    end
end
for (dest, bounds) in bound_dict
    println("Bounds for node $dest: ", bounds)
end
