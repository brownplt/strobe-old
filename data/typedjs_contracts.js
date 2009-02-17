// 'contracts' is defined in javascript-contracts.

var isTypeof = function(typeName) {
  return contracts.flat(typeName)(function(v) { 
    return typeof(v) == typeName; 
  });
};

var isBool = isTypeof("boolean");
var isString = isTypeof("string");
var isInt = contracts.flat("integer")(function(x) {
  return typeof(x) == "number" && (Math.floor(x) == x);
});
