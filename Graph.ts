///<reference path="lib/collections.ts"/>
///<reference path="lib/node.d.ts"/>

/** Graph module
*
*  Types for generic A\* implementation.
*
*  *NB.* The only part of this module
*  that you should change is the `aStarSearch` function. Everything
*  else should be used as-is.
*/

/** An edge in a graph. */
class Edge<Node> {
    from : Node;
    to   : Node;
    cost : number;
}

/** A directed graph. */
interface Graph<Node> {
    /** Computes the edges that leave from a node. */
    outgoingEdges(node : Node) : Edge<Node>[];
    /** A function that compares nodes. */
    compareNodes : collections.ICompareFunction<Node>;
}

/** Type that reports the result of a search. */
class SearchResult<Node> {
    /** The path (sequence of Nodes) found by the search algorithm. */
    path : Node[];
    /** The total cost of the path. */
    cost : number;
}

/**
* A\* search implementation, parameterised by a `Node` type. The code
* here is just a template; you should rewrite this function
* entirely. In this template, the code produces a dummy search result
* which just picks the first possible neighbour.
*
* Note that you should not change the API (type) of this function,
* only its body.
* @param graph The graph on which to perform A\* search.
* @param start The initial node.
* @param goal A function that returns true when given a goal node. Used to determine if the algorithm has reached the goal.
* @param heuristics The heuristic function. Used to estimate the cost of reaching the goal from a given Node.
* @param timeout Maximum time (in seconds) to spend performing A\* search.
* @returns A search result, which contains the path from `start` to a node satisfying `goal` and the cost of this path.
*/
function aStarSearch<Node> (
    graph : Graph<Node>,
    start : Node,
    goal : (n:Node) => boolean,
    heuristics : (n:Node) => number,
    timeout : number
) : SearchResult<Node> {
    var comparer: collections.ICompareFunction<Node> = function(a, b) {
        var aCost = costs.getValue(a) + heuristics(a), 
            bCost = costs.getValue(b) + heuristics(b);
        return bCost - aCost;
    }
    var queue = new collections.PriorityQueue(comparer);
    var paths = new collections.Dictionary<Node, Node>();
    var costs = new collections.Dictionary<Node, number>();
    queue.enqueue(start);
    costs.setValue(start, 0);

    var node : Node;
    while(!queue.isEmpty()) {
        node = queue.dequeue();
        if(goal(node))
            break;
        var nodeCost = costs.getValue(node);

        for(var edge of graph.outgoingEdges(node)) {
            var newNode : Node = edge.to;
            var newCost = nodeCost + edge.cost;
            if(!costs.containsKey(newNode) || newCost < costs.getValue(newNode)) {
                paths.setValue(newNode, node);
                costs.setValue(newNode, newCost);
                queue.enqueue(newNode);
            }
        }
    }
    if(!goal(node))
        return undefined; // no path

    var result : SearchResult<Node> = {
        path: [],
        cost: costs.getValue(node)
    };
    for(; node != start; node = paths.getValue(node))
        result.path.unshift(node);
    return result;
}


