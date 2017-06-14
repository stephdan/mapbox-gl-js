'use strict';

const parseColor = require('../util/parse_color');
const interpolate = require('../util/interpolate');

class RuntimeError extends Error {
    constructor(message) {
        super(message);
        this.name = 'ExpressionEvaluationError';
        this.message = message;
    }

    toJSON() {
        return `${this.name}: ${this.message}`;
    }
}

function assert(condition, message) {
    if (!condition) throw new RuntimeError(message);
    return true;
}

class Color {
    constructor(input) {
        if (Array.isArray(input)) {
            this.value = input;
        } else {
            this.value = parseColor(input);
            assert(typeof this.value !== 'undefined', `Could not parse color from value '${input}'`);
        }
    }
}

module.exports = () => ({
    error: (msg) => assert(false, msg),

    at: function (index, arrayOrVector) {
        assert(index < arrayOrVector.items.length, `${arrayOrVector.type} index out of bounds: ${index} > ${arrayOrVector.items.length}.`);
        return arrayOrVector.items[index];
    },

    get: function (obj, key, name) {
        assert(this.has(obj, key, name), `Property '${key}' not found in ${name || `object with keys: [${Object.keys(obj)}]`}`);
        const val = obj[key];
        return Array.isArray(val) ? this.vector('Vector<Value>', val) : val;
    },

    has: function (obj, key, name) {
        assert(obj, `Cannot get property ${key} from null object${name ? ` ${name}` : ''}.`);
        return this.as(obj, 'Object', name).hasOwnProperty(key);
    },

    typeOf: function (x) {
        if (x === null) return 'Null';
        else if (x.type === 'Vector<Value>') return 'Vector<Value>';
        else if (x instanceof Color) return 'Color';
        else return titlecase(typeof x);
    },

    as: function (value, expectedType, name) {
        const type = this.typeOf(value);
        assert(type === expectedType, `Expected ${name || 'value'} to be of type ${expectedType}, but found ${type} instead.`);
        return value;
    },

    coalesce: function (...thunks) {
        while (true) {
            try {
                return (thunks.shift())();
            } catch (e) {
                if (thunks.length === 0) throw e;
            }
        }
    },

    color: function (s) {
        return new Color(s);
    },

    array: function(type, items) {
        return {type, items};
    },

    vector: function(type, items) {
        return {type, items};
    },

    rgba: function (...components) {
        return new Color([
            components[0] / 255,
            components[1] / 255,
            components[2] / 255,
            components.length > 3 ? components[3] : 1
        ]);
    },

    evaluateCurve(input, stopInputs, stopOutputs, interpolation, resultType) {
        const stopCount = stopInputs.length;
        if (input <= stopInputs[0]) return stopOutputs[0]();
        if (input >= stopInputs[stopCount - 1]) return stopOutputs[stopCount - 1]();

        const index = findStopLessThanOrEqualTo(stopInputs, input);

        if (interpolation.name === 'step') {
            return stopOutputs[index]();
        }

        let base = 1;
        if (interpolation.name === 'exponential') {
            base = interpolation.base;
        }
        const t = interpolationFactor(input, base, stopInputs[index], stopInputs[index + 1]);

        return resultType === 'color' ?
            new Color(interpolate.color(stopOutputs[index]().value, stopOutputs[index + 1]().value, t)) :
            interpolate[resultType](stopOutputs[index](), stopOutputs[index + 1](), t);
    },

});

function titlecase (s) {
    return `${s.slice(0, 1).toUpperCase()}${s.slice(1)}`;
}

/**
 * Returns the index of the last stop <= input, or 0 if it doesn't exist.
 *
 * @private
 */
function findStopLessThanOrEqualTo(stops, input) {
    const n = stops.length;
    let lowerIndex = 0;
    let upperIndex = n - 1;
    let currentIndex = 0;
    let currentValue, upperValue;

    while (lowerIndex <= upperIndex) {
        currentIndex = Math.floor((lowerIndex + upperIndex) / 2);
        currentValue = stops[currentIndex];
        upperValue = stops[currentIndex + 1];
        if (input === currentValue || input > currentValue && input < upperValue) { // Search complete
            return currentIndex;
        } else if (currentValue < input) {
            lowerIndex = currentIndex + 1;
        } else if (currentValue > input) {
            upperIndex = currentIndex - 1;
        }
    }

    return Math.max(currentIndex - 1, 0);
}

/**
 * Returns a ratio that can be used to interpolate between exponential function
 * stops.
 * How it works: Two consecutive stop values define a (scaled and shifted) exponential function `f(x) = a * base^x + b`, where `base` is the user-specified base,
 * and `a` and `b` are constants affording sufficient degrees of freedom to fit
 * the function to the given stops.
 *
 * Here's a bit of algebra that lets us compute `f(x)` directly from the stop
 * values without explicitly solving for `a` and `b`:
 *
 * First stop value: `f(x0) = y0 = a * base^x0 + b`
 * Second stop value: `f(x1) = y1 = a * base^x1 + b`
 * => `y1 - y0 = a(base^x1 - base^x0)`
 * => `a = (y1 - y0)/(base^x1 - base^x0)`
 *
 * Desired value: `f(x) = y = a * base^x + b`
 * => `f(x) = y0 + a * (base^x - base^x0)`
 *
 * From the above, we can replace the `a` in `a * (base^x - base^x0)` and do a
 * little algebra:
 * ```
 * a * (base^x - base^x0) = (y1 - y0)/(base^x1 - base^x0) * (base^x - base^x0)
 *                     = (y1 - y0) * (base^x - base^x0) / (base^x1 - base^x0)
 * ```
 *
 * If we let `(base^x - base^x0) / (base^x1 base^x0)`, then we have
 * `f(x) = y0 + (y1 - y0) * ratio`.  In other words, `ratio` may be treated as
 * an interpolation factor between the two stops' output values.
 *
 * (Note: a slightly different form for `ratio`,
 * `(base^(x-x0) - 1) / (base^(x1-x0) - 1) `, is equivalent, but requires fewer
 * expensive `Math.pow()` operations.)
 *
 * @private
*/
function interpolationFactor(input, base, lowerValue, upperValue) {
    const difference = upperValue - lowerValue;
    const progress = input - lowerValue;

    if (base === 1) {
        return progress / difference;
    } else {
        return (Math.pow(base, progress) - 1) / (Math.pow(base, difference) - 1);
    }
}

