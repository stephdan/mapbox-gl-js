'use strict';

// @flow

const {
    NullType,
    NumberType,
    StringType,
    BooleanType,
} = require('./types');

const expressions = require('./expressions');

/*::
 import type { TypeError, TypedExpression } from './type_check.js';

 import type { ExpressionName } from './expression_name.js';

 export type ParseError = {|
     error: string,
     key: string
 |}
*/

module.exports = parseExpression;

/**
 * Parse raw JSON expression into a TypedExpression structure, with type
 * tags taken directly from the definition of each function (i.e.,
 * no inference performed).
 *
 * @private
 */
function parseExpression(expr: mixed, path: Array<number> = []) /*: TypedExpression | ParseError */ {
    const key = path.join('.');
    if (typeof expr === 'undefined') return {
        literal: true,
        value: null,
        type: NullType,
        key
    };

    if (typeof expr === 'string') return {
        literal: true,
        value: expr,
        type: StringType,
        key
    };

    if (typeof expr === 'number') return {
        literal: true,
        value: expr,
        type: NumberType,
        key
    };

    if (typeof expr === 'boolean') return {
        literal: true,
        value: expr,
        type: BooleanType,
        key
    };

    if (!Array.isArray(expr)) {
        return {
            key,
            error: `Expected an array, but found ${typeof expr} instead.`
        };
    }

    const op = expr[0];
    if (typeof op !== 'string') {
        return {
            key: `${key}.0`,
            error: `Expression name must be a string, but found ${typeof op} instead.`
        };
    }

    const definition = expressions[op];
    if (!definition) {
        return {
            key,
            error: `Unknown function ${op}`
        };
    }

    // special case parsing for `match`
    if (op === 'match') {
        if (expr.length < 3) return {
            key,
            error: `Expected at least 2 arguments, but found only ${expr.length - 1}.`
        };

        const inputExpression = parseExpression(expr[1], path.concat(1));
        if (inputExpression.error) return inputExpression;

        // parse input/output pairs.
        const matchInputs = [];
        const outputExpressions = [];
        for (let i = 2; i < expr.length - 2; i += 2) {
            const inputGroup = Array.isArray(expr[i]) ? expr[i] : [expr[i]];
            if (inputGroup.length === 0) {
                return {
                    key: `${key}.${i}`,
                    error: 'Expected at least one input value.'
                };
            }

            const parsedInputGroup = [];
            for (let j = 0; j < inputGroup.length; j++) {
                const parsedValue = parseExpression(inputGroup[j], path.concat(i, j));
                if (parsedValue.error) return parsedValue;
                if (!parsedValue.literal) return {
                    key: `${key}.${i}.${j}`,
                    error: 'Match inputs must be literal primitive values or arrays of literal primitive values.'
                };
                parsedInputGroup.push(parsedValue);
            }
            matchInputs.push(parsedInputGroup);

            const output = parseExpression(expr[i + 1], path.concat(i));
            if (output.error) return output;
            outputExpressions.push(output);
        }

        const otherwise = parseExpression(expr[expr.length - 1], path.concat(expr.length - 1));
        if (otherwise.error) return otherwise;
        outputExpressions.push(otherwise);

        return {
            literal: false,
            name: 'match',
            type: definition.type,
            matchInputs,
            arguments: [inputExpression].concat(outputExpressions),
            key
        };
    }

    const args = [];
    for (const arg of expr.slice(1)) {
        const parsedArg = parseExpression(arg, path.concat(1 + args.length));
        if (parsedArg.error) return parsedArg;
        args.push(parsedArg);
    }

    return {
        literal: false,
        name: op,
        type: definition.type,
        arguments: args,
        key
    };
}
