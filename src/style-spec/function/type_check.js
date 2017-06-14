'use strict';
// @flow

/*::
 import type { PrimitiveType, TypeName, VariantType, VectorType, ArrayType, AnyArrayType, NArgs, LambdaType, Type } from './types.js';

 import type { ExpressionName } from './expression_name.js';

 export type TypeError = {|
     error: string,
     key: string
 |}

 export type TypedLambdaExpression = {|
     literal: false,
     name: ExpressionName,
     type: LambdaType,
     arguments: Array<TypedExpression>,
     key: string,
     matchInputs?: Array<Array<TypedLiteralExpression>>
 |}

 export type TypedLiteralExpression = {|
     literal: true,
     value: string | number | boolean | null,
     type: Type,
     key: string
 |}

 export type TypedExpression = TypedLambdaExpression | TypedLiteralExpression

 */

const assert = require('assert');
const util = require('../../util/util');

const { lambda, array, vector, variant, nargs } = require('./types');

module.exports = typeCheckExpression;

// typecheck the given expression and return a new TypedExpression
// tree with all generics resolved
function typeCheckExpression(expected: Type, e: TypedExpression) /*: TypedExpression | {| errors: Array<TypeError> |} */ {
    if (e.literal) {
        const error = match(expected, e.type);
        if (error) return { errors: [{ key: e.key, error }] };
        return e;
    } else {
        // e is a lambda expression, so check its result type against the
        // expected type and recursively typecheck its arguments

        const typenames: { [string]: Type } = {};

        // The 'array' definition uses 'any_array' for its output type to
        // express that it produces arrays of arbitrary length.  Now that we're
        // checking a particular expression, refine its type tag to a fixed
        // length array based on the number of arguments that were provided to
        // ['array', ...].
        if (e.type.result.kind === 'any_array') {
            e.type.result = array(e.type.result.itemType, e.arguments.length);
        }

        if (expected.kind !== 'lambda') {
            // if the expected type is not a lambda, then check if it matches
            // the expression's output type, and then proceed with type checking
            // the arguments using e.type, which comes from the expression
            // definition.
            const error = match(expected, e.type.result, {}, typenames);
            if (error) return { errors: [{ key: e.key, error }] };
            expected = e.type;
        } else {
            const error = match(expected.result, e.type.result, typenames);
            if (error) return { errors: [{ key: e.key, error }] };
        }

        // Iterate through arguments to:
        //  - match expected argument type vs argument type, checking result type only -- don't recursively typecheck subexpressions at this stage
        //  - collect typename mappings when ^ succeeds or type errors when it fails
        //  - "unroll" NArgs by greedily matching them against argument values,
        //    building up an NArgs-free `expandedArgTypes` list in the process.
        const argValues = e.arguments;
        const expandedArgTypes = [];
        const errors = [];
        for (let vi = 0, ti = 0; vi < argValues.length && ti < expected.args.length; ti++) {
            const t = expected.args[ti];
            if (t.kind === 'nargs') {
                let sequenceCount = 0;
                let j = 0;
                let argTypeNames = {};
                while (
                    sequenceCount < t.N &&
                    vi < argValues.length &&
                    !match(t.types[j], argValues[vi].type, argTypeNames)
                ) {
                    vi++;
                    j = (j + 1) % t.types.length;
                    // If we've consumed a full sequence, append a copy of this
                    // list of types to the expanded argument list
                    if (j === 0) {
                        sequenceCount++;
                        expandedArgTypes.push.apply(expandedArgTypes, t.types);
                        util.extend(typenames, argTypeNames);
                        argTypeNames = {};
                    }
                }
                vi -= j;
            } else {
                const error = match(t, argValues[vi].type, typenames);
                if (error) errors.push({ key: e.key, error });
                expandedArgTypes.push(t);
                vi++;
            }
        }

        if (expandedArgTypes.length !== argValues.length) {
            errors.push({
                key: e.key,
                error: `Expected ${expandedArgTypes.length} arguments, but found ${argValues.length} instead.`
            });
        }

        const resultType = resolveTypenamesIfPossible(expected.result, typenames);

        if (isGeneric(resultType)) return {
            errors: [{key: e.key, error: `Could not resolve ${e.type.result.name}.  This expression must be wrapped in a type conversion, e.g. ["string", ${stringifyExpression(e)}].`}]
        };

        // If we already have errors, return early so we don't get duplicates when
        // we typecheck against the expanded/resolved argument types
        if (errors.length) return { errors };

        // resolve typenames and recursively type check argument expressions
        const resolvedArgTypes = [];
        const checkedArgs = [];
        for (let i = 0; i < expandedArgTypes.length; i++) {
            const t = expandedArgTypes[i];
            const arg = argValues[i];
            const expected = resolveTypenamesIfPossible(t, typenames);
            const result = typeCheckExpression(expected, arg);
            if (result.errors) {
                errors.push.apply(errors, result.errors);
            } else if (errors.length === 0) {
                resolvedArgTypes.push(expected);
                checkedArgs.push(result);
            }
        }

        // handle 'match' expression input values
        let matchInputs;
        if (e.matchInputs) {
            matchInputs = [];
            const inputType = resolvedArgTypes[0];
            for (const inputGroup of e.matchInputs) {
                const checkedGroup = [];
                for (const inputValue of inputGroup) {
                    const result = typeCheckExpression(inputType, inputValue);
                    if (result.errors) {
                        errors.push.apply(errors, result.errors);
                    } else {
                        checkedGroup.push(result);
                    }
                }
                matchInputs.push(checkedGroup);
            }
        }

        if (errors.length > 0) return { errors };

        const ret = {
            literal: false,
            name: e.name,
            type: lambda(resultType, ...resolvedArgTypes),
            arguments: checkedArgs,
            key: e.key,
            matchInputs
        };

        return ret;
    }
}

/**
 * Returns null if the type matches, or an error message if not.
 *
 * Also populate the given typenames maps: `expectedTypenames` maps typenames
 * from the scope of `expected` to Types, and `tTypenames` does the same for
 * typenames from t's typename scope.
 *
 * @private
 */
function match(expected: Type, t: Type, expectedTypenames: { [string]: Type } = {}, tTypenames: { [string]: Type } = {}) {
    const errorMessage = `Expected ${expected.name} but found ${t.name} instead.`;

    if (t.kind === 'lambda') t = t.result;

    if (expected.kind === 'typename') {
        if (!expectedTypenames[expected.typename] && !isGeneric(t)) {
            expectedTypenames[expected.typename] = t;
        }
        return null;
    }

    if (t.kind === 'typename' && !isGeneric(expected)) {
        if (!tTypenames[t.typename]) {
            tTypenames[t.typename] = expected;
        }
        t = expected;
    }

    if (expected.kind === 'primitive') {
        if (t === expected) return null;
        else return errorMessage;
    } else if (expected.kind === 'vector') {
        if (t.kind === 'vector') {
            const error = match(expected.itemType, t.itemType, expectedTypenames, tTypenames);
            if (error) return `${errorMessage}. (${error})`;
            else return null;
        } else {
            return errorMessage;
        }
    } else if (expected.kind === 'any_array' || expected.kind === 'array') {
        if (t.kind === 'array') {
            const error = match(expected.itemType, t.itemType, expectedTypenames, tTypenames);
            if (error) return `${errorMessage}. (${error})`;
            else if (expected.kind === 'array' && expected.N !== t.N) return errorMessage;
            else return null;
        } else {
            // technically we should check if t is a variant all of whose
            // members are Arrays, but it's probably not necessary in practice.
            return errorMessage;
        }
    } else if (expected.kind === 'variant') {
        if (t === expected) return null;

        for (const memberType of expected.members) {
            const mExpectedTypenames = util.extend({}, expectedTypenames);
            const mTTypenames = util.extend({}, tTypenames);
            const error = match(memberType, t, mExpectedTypenames, mTTypenames);
            if (!error) {
                util.extend(expectedTypenames, mExpectedTypenames);
                util.extend(tTypenames, mTTypenames);
                return null;
            }
        }

        // If t itself is a variant, then 'expected' must match each of its
        // member types in order for this to be a match.
        if (t.kind === 'variant') return t.members.some(m => match(expected, m, expectedTypenames, tTypenames)) ? errorMessage : null;

        return errorMessage;
    }

    throw new Error(`${expected.name} is not a valid output type.`);
}

function serializeExpression(e: TypedExpression, withTypes) {
    if (e.literal) {
        return e.value;
    } else {
        return [ e.name + (withTypes ? `: ${e.type.kind === 'lambda' ? e.type.result.name : e.type.name}` : '') ].concat(e.arguments.map(e => serializeExpression(e, withTypes)));
    }
}
function stringifyExpression(e: TypedExpression, withTypes) /*:string*/ {
    return JSON.stringify(serializeExpression(e, withTypes));
}

function isGeneric (type, stack = []) {
    if (stack.indexOf(type) >= 0) { return false; }
    if (type.kind === 'typename') {
        return true;
    } else if (type.kind === 'vector' || type.kind === 'array') {
        return isGeneric(type.itemType, stack.concat(type));
    } else if (type.kind === 'variant') {
        return type.members.some((t) => isGeneric(t, stack.concat(type)));
    }
    return false;
}

function resolveTypenamesIfPossible(type: Type, typenames: {[string]: Type}, stack = []) /*: Type */{
    assert(stack.indexOf(type) < 0, 'resolveTypenamesIfPossible() implementation does not support recursive variants.');

    if (!isGeneric(type)) return type;
    if (type.kind === 'typename') return typenames[type.typename] || type;

    const resolve = (t) => resolveTypenamesIfPossible(t, typenames, stack.concat(type));
    if (type.kind === 'vector') return vector(resolve(type.itemType, typenames));
    if (type.kind === 'array') return array(resolve(type.itemType, typenames), type.N);
    if (type.kind === 'variant') return variant(...type.members.map(resolve));
    if (type.kind === 'nargs') return nargs(type.N, ...type.types.map(resolve));
    if (type.kind === 'lambda') return lambda(resolve(type.result), ...type.args.map(resolve));

    assert(false, `Unsupported type ${type.kind}`);
    return type;
}

