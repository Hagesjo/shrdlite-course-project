///<reference path="World.ts"/>
///<reference path="Parser.ts"/>

/**
* Interpreter module
* 
* The goal of the Interpreter module is to interpret a sentence
* written by the user in the context of the current world state. In
* particular, it must figure out which objects in the world,
* i.e. which elements in the `objects` field of WorldState, correspond
* to the ones referred to in the sentence. 
*
* Moreover, it has to derive what the intended goal state is and
* return it as a logical formula described in terms of literals, where
* each literal represents a relation among objects that should
* hold. For example, assuming a world state where "a" is a ball and
* "b" is a table, the command "put the ball on the table" can be
* interpreted as the literal ontop(a,b). More complex goals can be
* written using conjunctions and disjunctions of these literals.
*
* In general, the module can take a list of possible parses and return
* a list of possible interpretations, but the code to handle this has
* already been written for you. The only part you need to implement is
* the core interpretation function, namely `interpretCommand`, which produces a
* single interpretation for a single command.
*/
module Interpreter {

    //////////////////////////////////////////////////////////////////////
    // exported functions, classes and interfaces/types

/**
Top-level function for the Interpreter. It calls `interpretCommand` for each possible parse of the command. No need to change this one.
* @param parses List of parses produced by the Parser.
* @param currentState The current state of the world.
* @returns Augments ParseResult with a list of interpretations. Each interpretation is represented by a list of Literals.
*/    
    export function interpret(parses : Parser.ParseResult[], currentState : WorldState) : InterpretationResult[] {
        var errors : Error[] = [];
        var interpretations : InterpretationResult[] = [];
        parses.forEach((parseresult) => {
            try {
                var result : InterpretationResult = <InterpretationResult>parseresult;
                result.interpretation = interpretCommand(result.parse, currentState);
                interpretations.push(result);
            } catch(err) {
                errors.push(err);
            }
        });
        if (interpretations.length) {
            return interpretations;
        } else {
            // only throw the first error found
            throw errors[0];
        }
    }

    export interface InterpretationResult extends Parser.ParseResult {
        interpretation : DNFFormula;
    }

    export type DNFFormula = Conjunction[];
    type Conjunction = Literal[];

    /**
    * A Literal represents a relation that is intended to
    * hold among some objects.
    */
    export interface Literal {
	/** Whether this literal asserts the relation should hold
	 * (true polarity) or not (false polarity). For example, we
	 * can specify that "a" should *not* be on top of "b" by the
	 * literal {polarity: false, relation: "ontop", args:
	 * ["a","b"]}.
	 */
        polarity : boolean;
	/** The name of the relation in question. */
        relation : string;
	/** The arguments to the relation. Usually these will be either objects 
     * or special strings such as "floor" or "floor-N" (where N is a column) */
        args : string[];
    }

    export function stringify(result : InterpretationResult) : string {
        return result.interpretation.map((literals) => {
            return literals.map((lit) => stringifyLiteral(lit)).join(" & ");
            // return literals.map(stringifyLiteral).join(" & ");
        }).join(" | ");
    }

    export function stringifyLiteral(lit : Literal) : string {
        return (lit.polarity ? "" : "-") + lit.relation + "(" + lit.args.join(",") + ")";
    }

    //////////////////////////////////////////////////////////////////////
    // private functions
    /**
     * The core interpretation function. The code here is just a
     * template; you should rewrite this function entirely. In this
     * template, the code produces a dummy interpretation which is not
     * connected to `cmd`, but your version of the function should
     * analyse cmd in order to figure out what interpretation to
     * return.
     * @param cmd The actual command. Note that it is *not* a string, but rather an object of type `Command` (as it has been parsed by the parser).
     * @param state The current state of the world. Useful to look up objects in the world.
     * @returns A list of list of Literal, representing a formula in disjunctive normal form (disjunction of conjunctions). See the dummy interpetation returned in the code for an example, which means ontop(a,floor) AND holding(b).
     */
    function interpretCommand(cmd : Parser.Command, state : WorldState) : DNFFormula {
        //console.log("===CMD=== " + JSON.stringify(cmd, null, 2) + "\n");
        if(cmd.command === "take" && cmd.entity.quantifier === "all")
            throw "we can't pick up more than one object";
        var subjects : Position[][];
        if(cmd.command === "put") {
            // we want manipulate the object in the arm
            if(state.holding === null)
                throw "we aren't holding anything";
            // this will break, eventually
            subjects = [[{objId: state.holding, stack: -1, posInStack: -1}]];
        } else {
            // figure out what objects we want to manipulate
            subjects = findEntities(cmd.entity, state);
        }

        //console.log("===SUBS=== " + JSON.stringify(subjects, null, 2));
        var ors : DNFFormula = [];
        if(cmd.command === "take") {
            // the object should end up in our arm
            for(var subs of subjects)
                ors.push([{polarity: true, relation: "holding", args: [subs[0].objId]}]);
        } else {
            // find all destinations, and since "all" is not viable we will always get an array in the form of
            // [[P], [Q], [R], ...], and as such we flatten it with map
            var dests : Position[] = findEntities(cmd.location.entity, state).map(x => x[0]);
            //console.log("===DEST=== " + JSON.stringify(dests, null, 2));
            for(var subs of subjects)
                ors = ors.concat(combine(cmd.location.relation, subs, dests, state));
        }
        if(!ors.length)
            throw "unable to interpret";
        return ors;
    }

    function combine(relation : string, lefts : Position[], rights : Position[], state : WorldState) : DNFFormula {
        var ors : DNFFormula = [];
        if(lefts.length === 1) {
            var left = lefts[0];
            var src_objId = left.objId;
            var src_obj = state.objects[src_objId];
            for(var right of rights) {
                var dest_objId = right.objId;
                var dest_obj = state.objects[dest_objId];
                if (src_objId !== dest_objId) {
                    // Here be dragons
                    // right.stack === undefined means that it's not an actual object (e.g. "floor")
                    if (right.stack === undefined || !
                        (
                         (relation === "inside" || relation === "ontop" || relation === "under") &&
                         (
                          (src_obj.size === "large" && dest_obj.size === "small") ||
                          (src_obj.form === "ball" && dest_obj.form !== "floor" && dest_obj.form !== "box" )
                         )
                        )
                       )
                        ors.push([{polarity: true, relation: relation, args: [src_objId, dest_objId]}]);
                }
            }
        } else {
            var left : Position = lefts.pop();
            for(var i : number = rights.length-1; i >= 0; i--) {
                var l : Position[] = lefts.slice();
                var r : Position[] = rights.slice();
                var right : Position = r.splice(i, 1)[0];
                var dnf : DNFFormula = combine(relation, l, r, state);
                for(var or of dnf)
                    or.push({polarity: true, relation: relation, args: [left.objId, right.objId]});
                ors = ors.concat(dnf);
            }
        }
        return ors;
    }

    interface Position {
        objId : string,
        // if stack and posInStack is not present then the object doesn't really have a position, like "floor"
        stack? : number, posInStack? : number
    }

    interface PositionTest {
        // x should always be pos
        test : (x : Position, y : Position) => boolean,
        pos : Position
    }

    function possToIdss(poss : Position[][], state : WorldState) : string[][] {
        return poss.map(pos => posToIds(pos, state));
    }

    function posToIds(pos : Position[], state : WorldState) : string[] {
        return pos.map(pos => posToId(pos, state));
    }

    function posToId(pos : Position, state : WorldState) : string {
        return pos.objId;
        //return state.stacks[pos.stack][pos.posInStack];
    }

    function findEntities(entity : Parser.Entity, state : WorldState) : Position[][] {
        if(entity.object.location !== undefined) {
            // there are more restrictions
            var tests : PositionTest[] = findLocations(entity.object.location, state);
            var objs  : Position[]     = findObjects(entity.object.object, state);
            var validObjs : Position[] = objs.filter(obj => tests.some(test => test.test(test.pos, obj)));
            return checkQuantifier(entity.quantifier, validObjs);
        } else {
            // entity.object describes what entities we want to find
            var objs : Position[] = findObjects(entity.object, state);
            return checkQuantifier(entity.quantifier, objs);
        }
    }

    function checkQuantifier(quantifier : string, entities : Position[]) : Position[][] {
        switch(quantifier) {
            case "the":
                if(entities.length > 1) // there can't be more than one "the"
                    throw "\"the\" is ambigous";
                return [entities];
            case "any":
                return entities.map(x => [x]);
            case "all":
                return [entities];

        }
        throw "unknown quantifier \"" + quantifier + "\"";
    }

    function findObjects(objectDesc : Parser.Object, state : WorldState) : Position[] {
        var entities : Position[] = [];
        if(objectDesc.form === "floor") {
            // so for some reason the parser thinks that "small blue floor" is an ok utterance
            // that's all good, except that the floor can't have a size or color...
            if(objectDesc.size !== null || objectDesc.color !== null) {
                throw("the floor can't have a size or color");
            }
            entities.push({objId: "floor"});
            return entities;
        }
        for(var stackIndex = 0; stackIndex < state.stacks.length; stackIndex++) {
            var stack : Stack = state.stacks[stackIndex];
            for(var objIndex = 0; objIndex < stack.length; objIndex++) {
                var objId : string = stack[objIndex];
                var object : ObjectDefinition = state.objects[objId];
                var form  : boolean = objectDesc.form  === null || objectDesc.form  === "anyform" || objectDesc.form  === object.form;
                var size  : boolean = objectDesc.size  === null || objectDesc.size  === object.size;
                var color : boolean = objectDesc.color === null || objectDesc.color === object.color;
                if(form && size && color){
                    entities.push({objId: objId, stack: stackIndex, posInStack: objIndex});
                }
            }
        }
        return entities;
    }

    function findLocations(location: Parser.Location, state : WorldState) : PositionTest[]  {
 
        if (location.entity.quantifier === "all")
            throw "\"all\" does not makes sense in this context";
       
        if (location.relation === "inside"){ 
            var form : string;
            if (location.entity.object.location === undefined)
                form = location.entity.object.form;
            else
                form = location.entity.object.object.form;

            if (form !== "box")
                throw("\"inside " + form + "\" does not make sense");
        }

        if (location.relation === "ontop"){
            var form : string;
            if (location.entity.object.location === undefined)
                form = location.entity.object.form;
            else
                form = location.entity.object.object.form;
            if (form === "ball")
                 throw("you can not put objects on balls")
        }


        var positions : Position[][] = findEntities(location.entity, state);
        var positionTest : PositionTest[] = [];
        switch(location.relation){
            case "leftof":
                for (var aoe of positions) {
                    if(aoe[0].stack === undefined) {
                        positionTest.push({pos: aoe[0], test: (x, y) => leftof(x.objId, y)});
                    } else {
                        positionTest.push({pos: aoe[0], test: (x, y) => y.stack < x.stack});
                    }
                }
                break;
            case "rightof":
                for (var aoe of positions) {
                    if(aoe[0].stack === undefined) {
                        positionTest.push({pos: aoe[0], test: (x, y) => rightof(x.objId, y)});
                    } else {
                        positionTest.push({pos: aoe[0], test: (x, y) => y.stack > x.stack});
                    }
                }
                break;
            case "inside":
            case "ontop":
                for (var aoe of positions) {
                    if(aoe[0].stack === undefined) {
                        positionTest.push({pos: aoe[0], test: (x, y) => ontop(x.objId, y)});
                    } else {
                        positionTest.push({pos: aoe[0], test: (x, y) => (y.stack == x.stack && (y.posInStack-1) == x.posInStack)});
                    }
                }
                break;
            case "under":
                for (var aoe of positions) {
                    if(aoe[0].stack === undefined) {
                        positionTest.push({pos: aoe[0], test: (x, y) => under(x.objId, y)});
                    } else {
                        positionTest.push({pos: aoe[0], test: (x, y) => (y.stack == x.stack && y.posInStack < x.posInStack)});
                    }
                }
                break;
            case "beside":
                for (var aoe of positions) {
                    if(aoe[0].stack === undefined) {
                        positionTest.push({pos: aoe[0], test: (x, y) => beside(x.objId, y)});
                    } else {
                        positionTest.push({pos: aoe[0], test: (x, y) => (Math.abs(y.stack - x.stack) == 1)});
                    }
                }
                break;
            case "above":
                for (var aoe of positions) {
                    if(aoe[0].stack === undefined) {
                        positionTest.push({pos: aoe[0], test: (x, y) => above(x.objId, y)});
                    } else {
                        positionTest.push({pos: aoe[0], test: (x, y) => (y.stack == x.stack && y.posInStack > x.posInStack)});
                    }
                }
                break;
        }
        return positionTest;
    }

    function leftof(objId : string, pos : Position) : boolean {
        throw("left of \"" + objId + "\" doesn't make sense");
    }

    function rightof(objId : string, pos : Position) : boolean {
        throw("right of \"" + objId + "\" doesn't make sense");
    }

    function ontop(objId : string, pos : Position) : boolean {
        switch(objId) {
            case "floor":
                return pos.posInStack === 0;
        }
        throw("on top \"" + objId + "\" doesn't make sense");
    }

    function under(objId : string, pos : Position) : boolean {
        throw("under \"" + objId + "\" doesn't make sense");
    }

    function beside(objId : string, pos : Position) : boolean {
        throw("beside \"" + objId + "\" doesn't make sense");
    }

    function above(objId : string, pos : Position) : boolean {
        throw("above \"" + objId + "\" doesn't make sense");
    }

    function literal(cmd : string, ...args : string[]) : Literal {
        /* Negation? */
        var pattern = /^-/g;
        var polarity: boolean = !pattern.test(cmd);
        
        /* Relation */
        pattern = /[^-]\w+/g;
        var relation: string  = pattern.exec(cmd).toString();

        /* Create Literal */
        var literal:Literal = {
            polarity : polarity,
            relation : relation,
            args : args
        };

        /* Testing 
        //console.log("pol: " + polarity);
        //console.log("rel: " + relation);
        //console.log("args: " + args); */

        return literal;
    }
}

