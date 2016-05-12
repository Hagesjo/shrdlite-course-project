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
        var subjects : string[][];
        if(cmd.command === "put") {
            // we want manipulate the object in the arm
            if(state.holding === null)
                throw "we aren't holding anything";
            subjects = [[state.holding]];
        } else {
            // figure out what objects we want to manipulate
            subjects = possToIdss(findEntities(cmd.entity, state), state);
        }

        //console.log("===SUBS=== " + JSON.stringify(subjects, null, 2));
        var ors : DNFFormula = [];
        if(cmd.command === "take") {
            // the object should end up in our arm
            for(var subs of subjects)
                ors.push([{polarity: true, relation: "holding", args: [subs[0]]}]);
        } else {
            // find all destinations, and since "all" is not viable we will always get an array in the form of
            // [[P], [Q], [R], ...], and as such we flatten it with map
            var dests : string[] = posToIds(findEntities(cmd.location.entity, state).map(x => x[0]), state);
            //console.log("===DEST=== " + JSON.stringify(dests, null, 2));
            for(var subs of subjects)
                ors = ors.concat(combine(cmd.location.relation, subs, dests, state));
        }
        if(!ors.length)
            throw "unable to interpret";
        return ors;
    }

    function combine(relation : string, lefts : string[], rights : string[], state : WorldState) : DNFFormula {
        var ors : DNFFormula = [];
        if(lefts.length === 1) {
            for(var right of rights) {
                var src_obj = state.objects[lefts[0]];
                var dest_obj = state.objects[right];
                if (lefts[0] !== right) {
                    // Here be dragons
                    if (!( (relation === "inside" ||
                          relation === "on top of") &&
                          src_obj.size === "large" &&
                          dest_obj.size === "small")) {
                        ors.push([{polarity: true, relation: relation, args: [lefts[0], right]}]);
                    }
                }
            }
        } else {
            var left : string = lefts.pop();
            for(var i : number = rights.length-1; i >= 0; i--) {
                var l : string[] = lefts.slice();
                var r : string[] = rights.slice();
                var right : string = r.splice(i, 1)[0];
                var dnf : DNFFormula = combine(relation, l, r, state);
                for(var or of dnf)
                    or.push({polarity: true, relation: relation, args: [left, right]});
                ors = ors.concat(dnf);
            }
        }
        return ors;
    }

    interface Position {
        stack : number, posInStack : number
    }

    interface PositionTest {
        test : (x : Position) => boolean
    }

    function possToIdss(poss : Position[][], state : WorldState) : string[][] {
        return poss.map(pos => posToIds(pos, state));
    }

    function posToIds(pos : Position[], state : WorldState) : string[] {
        return pos.map(pos => posToId(pos, state));
    }

    function posToId(pos : Position, state : WorldState) : string {
        return state.stacks[pos.stack][pos.posInStack];
    }

    function findEntities(entity : Parser.Entity, state : WorldState) : Position[][] {
        if(entity.object.location !== undefined) {
            // there are more restrictions
            var tests : PositionTest[] = findLocations(entity.object.location, state);
            var objs  : Position[]     = findObjects(entity.object.object, state);
            var validObjs : Position[] = objs.filter(obj => tests.some(test => test.test(obj)));
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
        for(var stackIndex = 0; stackIndex < state.stacks.length; stackIndex++) {
            var stack : Stack = state.stacks[stackIndex];
            for(var objIndex = 0; objIndex < stack.length; objIndex++) {
                var objId : string = stack[objIndex];
                var object : ObjectDefinition = state.objects[objId];
                var form  : boolean = objectDesc.form  === null || objectDesc.form  === object.form;
                var size  : boolean = objectDesc.size  === null || objectDesc.size  === object.size;
                var color : boolean = objectDesc.color === null || objectDesc.color === object.color;
                if(form && size && color)
                    entities.push({stack: stackIndex, posInStack: objIndex});
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

        if (location.relation === "on top of"){
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
                for (var pos of positions) 
                    positionTest.push({test: x => x.stack < pos[0].stack});
                break;
            case "rightof":
                for (var pos of positions)
                    positionTest.push({test: x => x.stack > pos[0].stack}); 
                break;
            case "inside":
            case "ontop":
                for (var pos of positions)
                    positionTest.push({test: x => (x.stack == pos[0].stack && (x.posInStack-1) == pos[0].posInStack)});
                break;
            case "under":
                for (var pos of positions)
                    positionTest.push({test: x => (x.stack == pos[0].stack && x.posInStack < pos[0].posInStack)});
                break;
            case "beside":
                for (var pos of positions) 
                    positionTest.push({test: x => (Math.abs(x.stack - pos[0].stack) == 1)});
                break;
            case "above":
                for (var pos of positions)
                    positionTest.push({test: x => (x.stack == pos[0].stack && x.posInStack > pos[0].posInStack)});
                break;
        } 
        return positionTest;
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

