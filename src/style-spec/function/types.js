'use strict';
// @flow

/*::
 export type PrimitiveType = { kind: 'primitive', name: string }
 export type TypeName = { kind: 'typename', name: string, typename: string }
 export type VariantType = { kind: 'variant', name: string, members: Array<Type> }
 export type VectorType = { kind: 'vector', name: string, itemType: Type }
 export type ArrayType = { kind: 'array', name: string, itemType: Type, N: number }
 export type AnyArrayType = { kind: 'any_array', name: string, itemType: Type }
 export type NArgs = { kind: 'nargs', name: string, types: Array<Type>, N: number }
 export type LambdaType = { kind: 'lambda', name: string, result: Type, args: Array<Type> }
 export type Type = PrimitiveType | TypeName | VariantType | VectorType | ArrayType | AnyArrayType | NArgs | LambdaType
*/

function primitive(name) /*: PrimitiveType */ {
    return { kind: 'primitive', name };
}

function typename(tn: string)/*: TypeName */ {
    return { kind: 'typename', name: `typename ${tn}`, typename: tn };
}

// each 'types' argument may be either an object of type Type or a function
// accepting 'this' variant and returning a Type (the latter allowing
// recursive variant definitions)
function variant(...types: Array<Type | (Type)=>Type>) /*: VariantType */ {
    const v: Object = {
        kind: 'variant',
        name: '(recursive_wrapper)'
    };
    v.members = types.map(t => typeof t === 'function' ? t(v) : t);
    v.name = `Variant<${v.members.map(t => t.name).join(' | ')}>`;
    v.toJSON = function () { return this.name; };
    return v;
}

function vector(itemType: Type) /*: VectorType */ {
    return {
        kind: 'vector',
        name: `Vector<${itemType.name}>`,
        itemType
    };
}

function array(itemType: Type, N: number) /*: ArrayType */ {
    return {
        kind: 'array',
        name: `Array<${itemType.name}, ${N}>`,
        itemType,
        N
    };
}

// Used to match an argument that must be an array of some (unspecified)
// length.
function anyArray(itemType: Type) /*: AnyArrayType */ {
    return {
        kind: 'any_array',
        name: `Array<${itemType.name}, N>`,
        itemType
    };
}

function nargs(N: number, ...types: Array<Type>) /*: NArgs */ {
    return {
        kind: 'nargs',
        name: `${types.map(t => t.name).join(', ')}, ...`,
        types,
        N
    };
}

function lambda(result: Type, ...args: Array<Type>) /*: LambdaType */ {
    return {
        kind: 'lambda',
        name: `(${args.map(a => a.name).join(', ')}) => ${result.name}`,
        result,
        args
    };
}

const NullType = primitive('null');
const NumberType = primitive('number');
const StringType = primitive('string');
const BooleanType = primitive('boolean');
const ColorType = primitive('color');
const ObjectType = primitive('object');

const ValueType = variant(
    NullType,
    NumberType,
    StringType,
    BooleanType,
    ColorType,
    ObjectType,
    (Value: Type) => vector(Value)
);

const InterpolationType = primitive('interpolation_type');

module.exports = {
    NullType,
    NumberType,
    StringType,
    BooleanType,
    ColorType,
    ObjectType,
    ValueType,
    InterpolationType,
    typename,
    variant,
    vector,
    array,
    anyArray,
    lambda,
    nargs
};
