///<reference path="World.ts"/>
///<reference path="Interpreter.ts"/>
///<reference path="Graph.ts"/>
///<reference path="GridGraph.ts"/>


/** 
 * Planner module
 *
 * The goal of the Planner module is to take the interpetation(s)
 * produced by the Interpreter module and to plan a sequence of actions
 * for the robot to put the world into a state compatible with the
 * user's command, i.e. to achieve what the user wanted.
 *
 */
module Planner {

    //////////////////////////////////////////////////////////////////////
    // exported functions, classes and interfaces/types

    /**
     * Top-level driver for the Planner. Calls `planInterpretation` for each given interpretation generated by the Interpreter. 
     * @param interpretations List of possible interpretations.
     * @param currentState The current state of the world.
     * @returns Augments Interpreter.InterpretationResult with a plan represented by a list of strings.
     */
    export function plan(interpretations : Interpreter.InterpretationResult[], currentState : WorldState) : PlannerResult[] {
        var errors : Error[] = [];
        var plans : PlannerResult[] = [];
        interpretations.forEach((interpretation) => {
            try {
                var result : PlannerResult = <PlannerResult>interpretation;
                result.plan = planInterpretation(result.interpretation, currentState);
                if (result.plan.length == 0) {
                    result.plan.push("That is already true!");
                }
                plans.push(result);
            } catch(err) {
                errors.push(err);
            }
        });
        if (plans.length) {
            return plans;
        } else {
            // only throw the first error found
            throw errors[0];
        }
    }

    export interface PlannerResult extends Interpreter.InterpretationResult {
        plan : string[];
    }

    export function stringify(result : PlannerResult) : string {
        return result.plan.join(", ");
    }

    //////////////////////////////////////////////////////////////////////
    // private functions

    /**
     * The core of the Planner
     *
     * @param interpretation The logical interpretation of the user's desired goal. The plan needs to be such that by executing it, the world is put into a state that satisfies this goal.
     * @param state The current world state.
     * @returns Basically, a plan is a
     * stack of strings, which are either system utterances that
     * explain what the robot is doing (e.g. "Moving left") or actual
     * actions for the robot to perform, encoded as "l", "r", "p", or
     * "d". The code shows how to build a plan. Each step of the plan can
     * be added using the `push` method.
     */
    function planInterpretation(interpretation : Interpreter.DNFFormula, state : WorldState) : string[] {
        var graph = new PGraph(state.objects);
        var startNode = new PNode(state.stacks, state.holding, state.arm, null);
        var goalFun = (node : PNode) => goal(interpretation, node);
        var heuristicsFun = (node : PNode) => heuristics(interpretation, node);
        var timeout = 5;
        var aStar = aStarSearch(graph, startNode, goalFun, heuristicsFun, timeout);
        if(!aStar)
            throw("that's impossible");
        var plan : string[] = [];
        // Recreate the sequence of actions taken to get to the goal.
        for(var node of aStar.path)
            plan.push(node.action);
        return plan;
    }

}

/**
 * goal function
 * Tests if the PNode, which represents a state in the world, is the goal state. This is done by
 * checking that the state fullfils the conditions provided by the logical interpretation.
 * @param interpretation The logical interpretation of the user's desired goal.
 * @param n A PNode which contains the current state of the world.
 * @returns A boolean which determines whether the current state of the world is the goal state.
 */

function goal(interpretation : Interpreter.DNFFormula, n: PNode) : boolean {
    for (var i = 0; i < interpretation.length; i++) {
        var condSatisfied : boolean = true;

        for (var j = 0; j < interpretation[i].length; j++) {
            var condition = interpretation[i][j];
            var firstArg : string = condition.args[0]; // Get the first object.

            if (condition.relation === "holding") {
                if (n.holding !== firstArg) {
                    condSatisfied = false; // The arm is not holding the specified object.
                    break;
                }
            } else {
                var secArg : string = condition.args[1]; // Get second object.
                if(n.holding === firstArg || n.holding === secArg) {
                    condSatisfied = false; // If the arm holds any of the argument objects the condition is not satified, given that the relation is not holding.
                    break;
                }
                var firstCord : Coordinate = findIndex(firstArg, n.stacks); // Get the coordinate of the first argument object.

                if(secArg === "floor") {
                    switch(condition.relation) {
                        case "ontop":
                            if(firstCord.y !== 0)
                                condSatisfied = false; // Check if an object is not on the floor
                            break;
                        case "above":
                            break;
                    }
                } else {
                    var secCord : Coordinate = findIndex(secArg, n.stacks); // Get coordinate of second argument object.

                    switch(condition.relation) {
                        case "leftof":
                            /* Is the first object right of the second object? */
                            if (firstCord.x >= secCord.x)
                                condSatisfied = false;    
                            break;
                        case "rightof":
                            /* Is the first object left of the second object? */
                            if (firstCord.x <= secCord.x) 
                                condSatisfied = false;
                            break;
                        case "above":
                            /* Are the objects not at the same X-Coordinate or is the first object under the second object? */
                            if (firstCord.x !== secCord.x || firstCord.y <= secCord.y) 
                                condSatisfied = false;
                            break;
                        case "under":
                            /* Are the objects not at the same X-Coordinate or is the first object above the second object?  */
                            if (firstCord.x !== secCord.x || firstCord.y >= secCord.y)
                                condSatisfied = false;
                            break;
                        case "beside":
                            /* Is the X-distance between the objects equal to 1?  */
                            if (Math.abs(firstCord.x - secCord.x) !== 1)
                                condSatisfied = false; 
                            break;
                        case "ontop":
                        case "inside":
                            /* Are the objects not at the same X-Coordinate or is the Y-distance not equal to 1?  */
                            if (firstCord.x !== secCord.x || firstCord.y - secCord.y !== 1)
                                condSatisfied = false; 
                            break;
                    }
                }
            }       
        }
        // If all conditions are satisfied in the DNFFormula we have found a solution.
        if (condSatisfied)
            return true;
    }
    return false;
}

/** 
 * heuristics function
 * Given a PNode (state) and the DNFFormula determines how far the given state is from the goal.
 * @param ors The logical interpretation of the user's desired goal.
 * @param node The PNode (state) that you want to check.
 * @returns An integer which represents the distance from the given state to the goal state.
 */

function heuristics(ors : Interpreter.DNFFormula, node : PNode) : number {
    var min : number = Infinity;
    for(var ands of ors) {
        var andMin : number = 0;
        for(var and of ands) {
            switch(and.relation) {
                case "holding":
                    if(node.holding === and.args[0]) {
                    // do nothing
                    } else {
                        var srcCoord = findIndex(and.args[0], node.stacks);
                        if(node.holding !== null)
                            andMin++; // drop whatever it is we're holding
                        andMin += Math.abs(node.arm - srcCoord.x); // move the arm above src
                        andMin++; // pick
                    }
                    break;
                default:
                    if(node.holding === and.args[0]) {
                        if(and.args[1] === "floor") {
                            //TODO find nearest empty stack
                            andMin++; // drop
                        } else {
                            var dstCoord : Coordinate = findIndex(and.args[1], node.stacks);
                            andMin += Math.abs(dstCoord.x - node.arm); // move the arm above dst
                            if(and.relation === "beside")
                                andMin++; // worst case we have to put it on the far side
                            andMin++; // drop
                        }
                    } else if(node.holding === and.args[1]) {
                        var srcCoord : Coordinate = findIndex(and.args[0], node.stacks);
                        var dstCoord : Coordinate = {x: node.arm, y: node.stacks[node.arm].length};
                        andMin++; // drop dst
                        andMin += Math.abs(node.arm - srcCoord.x); // move the arm above src
                        andMin++; // pickup
                        andMin += Math.abs(dstCoord.x - srcCoord.x); // move the arm above dst
                        andMin++; // drop
                    } else {
                        if(node.holding !== null)
                            andMin++; // drop whatever it is we're holding
                        var srcCoord : Coordinate = findIndex(and.args[0], node.stacks);
                        andMin += Math.abs(node.arm - srcCoord.x); // move the arm above src
                        andMin++; // pickup
                        if(and.args[1] === "floor") {
                            //TODO find nearest empty stack
                            andMin++; // move to adjacent stack
                            andMin++; // drop
                        } else {
                            var dstCoord : Coordinate = findIndex(and.args[1], node.stacks);
                            andMin += Math.abs(dstCoord.x - srcCoord.x); // move the arm above dst
                            if(and.relation === "beside")
                                andMin++; // worst case we have to put it on the far side
                            andMin++; // drop
                        }
                    }
                    break;
            }
        }
        min = Math.min(min, andMin);
    }
    return min;
}

/** 
 * function findIndex
 * Finds the Coordinate for the position of the object in the world.
 * @param obj The object you want to find the Coordinate for.
 * @param stacks The stack.
 * @returns Coordinate of the object in the world.
*/

function findIndex(obj : string, stacks : Stack[]) {
    var coordinate : Coordinate = undefined;

    for (var i = 0; i < stacks.length; i++){
        for (var j = 0; j < stacks[i].length; j++) {
            if (stacks[i][j] === obj) {
                return {x:i, y:j};
            }
        }
    }

    throw("no index for " + obj);
}

/**
 * PGraph class
 * A Graph which contains PNodes (states). Used in combination with the aStarSearch.
 */

class PGraph implements Graph<PNode> {

    constructor(public objects : {[s:string]: ObjectDefinition;}) {} // All objects in the world.

    outgoingEdges(node: PNode) : Edge<PNode>[] {
        // Caution: Don't create side-effects when creating new states. 
        var edges : Edge<PNode>[] = [];
        if(node.arm > 0) { // Can the arm move left?
            var left : PNode = new PNode(node.stacks, node.holding, node.arm, "l"); 
            left.arm--;
            edges.push({from: node, to: left, cost: 1});
        }
        if(node.arm < node.stacks.length - 1) { // Can the arm move right?
            var right : PNode = new PNode(node.stacks, node.holding, node.arm, "r");
            right.arm++;
            edges.push({from: node, to: right, cost: 1});
        }
        if(node.holding === null && node.stacks[node.arm].length) { // Can we pick up something and is the stack not empty?
            var pick : PNode = new PNode(node.stacks.slice(), node.holding, node.arm, "p");
            pick.stacks[pick.arm] = pick.stacks[pick.arm].slice();
            pick.holding = pick.stacks[pick.arm].pop();
            edges.push({from: node, to: pick, cost: 1});
        }
        if(node.holding !== null && node.stacks[node.arm].length < node.stacks.length) { // Can we drop something and is the stack not full?
            var physicsOk : boolean = node.stacks[node.arm].length === 0;
            if(!physicsOk) { // We don't have to check physics if the stack is empty.
                var srcId    : string           = node.holding;
                var srcObj   : ObjectDefinition = this.objects[srcId];
                var dstId    : string           = node.stacks[node.arm][node.stacks[node.arm].length-1];
                var dstObj   : ObjectDefinition = this.objects[dstId];
                var relation : string           = dstObj.form === "box" ? "inside" : "ontop";
                physicsOk = Interpreter.checkPhysics(srcId, srcObj, relation, dstId, dstObj)
            }
            if(physicsOk) {
                var drop : PNode = new PNode(node.stacks.slice(), node.holding, node.arm, "d");
                drop.stacks[drop.arm] = drop.stacks[drop.arm].slice();
                drop.stacks[drop.arm].push(drop.holding);
                drop.holding = null;
                edges.push({from: node, to: drop, cost: 1});
            }
        }
        return edges;
    }

    // This is never used in our aStarSearch implementation.
    compareNodes : collections.ICompareFunction<PNode> = function (a : PNode, b : PNode) {
        return undefined;
    } 

}

/** class PNode
 * A node which represents a state in the world.
 */
class PNode {

    constructor (
        public stacks : Stack[], // The stack.
        public holding : string, // Which object the arm is currently holding.
        public arm : number, // The X-Coordinate of the arm.
        public action : string // Which actions was taken to get to this state i.e "d", "r", "l" or "p"
    ) {}

    /* Because the string representation of any object is obviously [Object object] */
    public toString = () : string => JSON.stringify(this);

}
