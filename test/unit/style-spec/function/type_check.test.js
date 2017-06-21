'use strict';

const test = require('mapbox-gl-js-test').test;
const {
    StringType,
    NumberType,
    typename,
    lambda,
    vector,
    variant
} = require('../../../../src/style-spec/function/types');
const typecheck = require('../../../../src/style-spec/function/type_check');

test('typecheck expressions', (t) => {
//     t.test('literal', (t) => {
//         const value = {
//             literal: true,
//             value: 'hello',
//             type: StringType
//         };
//         const result = typecheck(StringType, value);
//         t.deepEqual(result, value);
//         t.end();
//     });
// 
//     t.test('literal wrong type', (t) => {
//         const value = {
//             literal: true,
//             value: 1,
//             type: NumberType
//         };
//         const result = typecheck(StringType, value);
//         t.ok(result.errors);
//         t.end();
//     });
// 
//     t.test('check value tagged with non-generic lambda type', (t) => {
//         const value = {
//             literal: false,
//             name: 'fn',
//             type: lambda(NumberType, StringType),
//             arguments: [{literal: true, value: '', type: StringType}],
//             key: '',
//             matchInputs: null
//         };
// 
//         t.deepEqual(typecheck(NumberType, value), value);
// 
//         t.deepEqual(typecheck(lambda(NumberType, StringType), value), value);
//         t.deepEqual(typecheck(lambda(typename('T'), StringType), value), value);
//         t.deepEqual(typecheck(lambda(NumberType, typename('U')), value), value);
//         t.deepEqual(typecheck(lambda(variant(NumberType, StringType), StringType), value), value);
// 
//         t.ok(typecheck(lambda(StringType, StringType), value).errors);
//         t.ok(typecheck(lambda(NumberType, NumberType), value).errors);
//         t.end();
//     });

//    t.test('check value tagged with lambda type having generic result type', (t) => {
//        const value = {
//            literal: false,
//            name: 'fn',
//            type: lambda(typename('T'), StringType),
//            arguments: [{literal: true, value: '', type: StringType}],
//            key: '',
//            matchInputs: null
//        };
//
//        t.deepEqual(
//            typecheck(NumberType, value).type,
//            lambda(NumberType, StringType)
//        );
//
//        t.deepEqual(
//            typecheck(StringType, value).type,
//            lambda(StringType, StringType)
//        );
//
//        t.deepEqual(
//            typecheck(lambda(NumberType, StringType), value).type,
//            lambda(NumberType, StringType)
//        );
//
//        t.deepEqual(
//            typecheck(lambda(NumberType, typename('T')), value).type,
//            lambda(NumberType, StringType)
//        );
//
//        t.equal(
//            typecheck(lambda(variant(NumberType, StringType), StringType), value).type.name,
//            lambda(variant(NumberType, StringType), StringType).name
//        );
//
//        t.ok(typecheck(lambda(StringType, NumberType), value).errors);
//        t.end();
//    });

    t.test('check value tagged with lambda type having generic input and result type', (t) => {
        const value = {
            literal: false,
            name: 'fn',
            type: lambda(typename('T'), typename('T'), StringType),
            arguments: [{literal: true, value: 0, type: NumberType}, {literal: true, value: '', type: StringType}],
            key: '',
            matchInputs: null
        };

        t.deepEqual(
            typecheck(NumberType, value).type,
            lambda(NumberType, NumberType, StringType)
        );

        t.ok(typecheck(StringType, value).errors);

        value.arguments[0] = {literal: true, value: '', type: StringType};
        t.deepEqual(
            typecheck(StringType, value).type,
            lambda(StringType, StringType, StringType)
        );

        t.deepEqual(
            typecheck(lambda(StringType, StringType, StringType), value).type,
            lambda(StringType, StringType, StringType)
        );

        t.deepEqual(
            typecheck(lambda(typename('T'), typename('T'), StringType), value).type,
            lambda(StringType, StringType, StringType)
        );

        t.deepEqual(
            typecheck(lambda(typename('U'), typename('U'), StringType), value).type,
            lambda(StringType, StringType, StringType)
        );

        t.deepEqual(
            typecheck(typename('T'), value).type,
            lambda(StringType, StringType, StringType)
        );

        t.deepEqual(
            typecheck(typename('U'), value).type,
            lambda(StringType, StringType, StringType)
        );

        t.end();
    });

    t.test('check value tagged with lambda type having generic input and result type, and a nested generic argument value', (t) => {
        const value = {
            literal: false,
            name: 'fn',
            type: lambda(typename('T'), typename('T'), StringType),
            arguments: [{
                literal: false,
                name: 'fn2',
                type: lambda(typename('T'), typename('T')),
                arguments: [{literal: true, value: '', type: StringType}]
            }, {literal: true, value: '', type: StringType}],
            key: '',
            matchInputs: null
        };

        const result = typecheck(StringType, value);
        t.deepEqual(result.type, lambda(StringType, StringType, StringType));
        t.deepEqual(result.arguments[0].type, lambda(StringType, StringType));

        value.arguments[0] = {
            literal: false,
            name: 'fn2',
            type: lambda(typename('U'), typename('U')),
            arguments: [{literal: true, value: '', type: StringType}]
        };

        t.deepEqual(
            typecheck(StringType, value).type,
            lambda(StringType, StringType, StringType)
        );

        value.arguments[0] = {
            literal: false,
            name: 'fn2',
            type: lambda(typename('U'), typename('U')),
            arguments: [{literal: true, value: 0, type: NumberType}]
        };

        t.ok(typecheck(StringType, value).errors);
        t.deepEqual(
            typecheck(NumberType, value).type,
            lambda(NumberType, NumberType, StringType)
        );

        t.ok(
            typecheck(typename('T'), value).errors,
            'Type inference does not look ahead more than one level in the AST'
        );

        t.end();
    });


    t.end();
});
