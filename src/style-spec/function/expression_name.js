'use strict';

// This would ideally be in expressions.js, but pulled into separate file
// to avoid circular imports, due to https://github.com/facebook/flow/issues/3249

/*::
 export type ExpressionName = "literal" | "ln2" | "pi" | "e" | "string" | "number" | "boolean" | "json_array" | "object" | "get" | "has" | "at" | "typeof" | "length" | "zoom" | "properties" | "geometry_type" | "id" | "case" | "match" | "coalesce" | "==" | "!=" | ">" | ">=" | "<=" | "<" | "&&" | "||" | "!" | "curve" | "step" | "exponential" | "linear" | "cubic-bezier" | "+" | "-" | "*" | "/" | "%" | "^" | "log10" | "ln" | "log2" | "sin" | "cos" | "tan" | "asin" | "acos" | "atan" | "ceil" | "floor" | "round" | "abs" | "min" | "max" | "concat" | "upcase" | "downcase" | "rgb" | "rgba" | "color" | "color_to_array"
*/
