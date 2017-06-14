'use strict';
// @flow

const assert = require('assert');

module.exports = compileExpression;

const expressions = require('./expressions');
const parseExpression = require('./parse');
const typecheck = require('./type_check');
const evaluationContext = require('./evaluation_context');

/*::
 import type { PrimitiveType, TypeName, VariantType, VectorType, ArrayType, AnyArrayType, NArgs, LambdaType, Type } from './types.js';

 import type { TypeError, TypedLambdaExpression, TypedLiteralExpression, TypedExpression } from './type_check.js';

 import type { ExpressionName } from './expression_name.js';

 export type CompiledExpression = {|
     result: 'success',
     js: string,
     type: Type,
     isFeatureConstant: boolean,
     isZoomConstant: boolean,
     expression: TypedExpression,
     function?: Function
 |}


 type CompileError = {|
     error: string,
     key: string
 |}

 type CompileErrors = {|
     result: 'error',
     errors: Array<CompileError>
 |}
 */

/**
 *
 * Given a style function expression object, returns:
 * ```
 * {
 *   result: 'success',
 *   isFeatureConstant: boolean,
 *   isZoomConstant: boolean,
 *   js: string,
 *   function: Function
 * }
 * ```
 * or else
 *
 * ```
 * {
 *   result: 'error',
 *   errors: Array<CompileError>
 * }
 * ```
 *
 * @private
 */
function compileExpression(expr: mixed) {
    const parsed = parseExpression(expr);
    if (parsed.error) {
        return {
            result: 'error',
            errors: [parsed]
        };
    }

    if (parsed.type) {
        const typecheckResult = typecheck(parsed.type, parsed);
        if (typecheckResult.errors) {
            return { result: 'error', errors: typecheckResult.errors };
        }

        const compiled = compile(null, typecheckResult);
        if (compiled.result === 'success') {
            const fn = new Function('mapProperties', 'feature', `
    mapProperties = mapProperties || {};
    feature = feature || {};
    var props = feature.properties || {};
    return (${compiled.js})
    `);
            compiled.function = fn.bind(evaluationContext());
        }

        return compiled;
    }

    assert(false, 'parseExpression should always return either error or typed expression');
}

function compile(expected: Type | null, e: TypedExpression) /*: CompiledExpression | CompileErrors */ {
    if (e.literal) {
        return {
            result: 'success',
            js: JSON.stringify(e.value),
            type: e.type,
            isFeatureConstant: true,
            isZoomConstant: true,
            expression: e
        };
    } else {
        const errors: Array<CompileError> = [];
        const compiledArgs: Array<CompiledExpression> = [];

        for (let i = 0; i < e.arguments.length; i++) {
            const arg = e.arguments[i];
            const argType = e.type.args[i];
            const compiledArg = compile(argType, arg);
            if (compiledArg.result === 'error') {
                errors.push.apply(errors, compiledArg.errors);
            } else if (compiledArg.result === 'success') {
                compiledArgs.push(compiledArg);
            }
        }

        if (errors.length > 0) {
            return { result: 'error', errors };
        }

        let isFeatureConstant = compiledArgs.reduce((memo, arg) => memo && arg.isFeatureConstant, true);
        let isZoomConstant = compiledArgs.reduce((memo, arg) => memo && arg.isZoomConstant, true);

        const definition = expressions[e.name];
        const compiled = definition.compile(e, compiledArgs);
        if (compiled.errors) {
            return {
                result: 'error',
                errors: compiled.errors.map(message => ({ error: message, key: e.key }))
            };
        }

        if (typeof compiled.isFeatureConstant === 'boolean') {
            isFeatureConstant = isFeatureConstant && compiled.isFeatureConstant;
        }
        if (typeof compiled.isZoomConstant === 'boolean') {
            isZoomConstant = isZoomConstant && compiled.isZoomConstant;
        }

        assert(compiled.js);

        return {
            result: 'success',
            js: `(${compiled.js || 'void 0'})`, // `|| void 0` is to satisfy flow
            type: e.type.result,
            isFeatureConstant,
            isZoomConstant,
            expression: e
        };
    }
}

