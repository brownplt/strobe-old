function() :: (->) {
  function stringToJSON(s) :: (String -> string) {
/*    function gsub(s, pattern, replacement) :: (String, RegExp, {
    var result = '', source = this, match;
    replacement = arguments.callee.prepareReplacement(replacement);

    while (source.length > 0) {
      if (match = source.match(pattern)) {
        result += source.slice(0, match.index);
        result += String.interpret(replacement(match));
        source  = source.slice(match.index + match[0].length);
      } else {
        result += source, source = '';
      }
    }
    return result;
  },

    function inspect(useDoubleQuotes) :: (bool -> string){
      var escapedString = s.gsub(
          /[\x00-\x1f\\]/,
          function(match) :: (  {
            var character = String.specialChar[match[0]];
            return character ? character : '\\u00' + match[0].charCodeAt().toPaddedString(2, 16);
      });
      if (useDoubleQuotes)
        return '"' + escapedString.replace(/"/g, '\\"') + '"';
      return "'" + escapedString.replace(/'/g, '\\\'') + "'";
    };

    return s.inspect(true);*/
    return ""+s; //add real functions later.
  };

  function toJSON(object) :: (any -> string?) {
    function isElement(object) :: {nodeType :: int?}? -> bool {
      //return !!(object && object.nodeType == 1);
      if (typeof object != "undefined") {
        if (object.nodeType == 1) return true;
      }
      return false;
    };


    var type = typeof object;
    switch (type) {
      case 'undefined':
      case 'function':
      case 'unknown': return;
      case 'boolean': return object.toString();
    }

    //if (object === null) return 'null';
    //prototype assumes we have an object, now.
    //i wonder how it treats numbers and such...
    //if (type != "object") return;
    var tmpobj = {};

    //if (object.toJSON) return object.toJSON();
    //if (isElement(object)) return;

    var results :: Array<string> = [];
    for (var property in tmpobj) {
      var value = toJSON(tmpobj[property]);
      if (!(typeof value == "undefined")) //Object.isUndefined(value))
        results.push(stringToJSON(property) + ': ' + value);
    }
    //fix once arrays can be objects:
    //return '{' + results.join(', ') + '}';
    return '{ fakened }';
  };
} :: (->);


/*
function escapeString(s) :: (string -> string) {
  return '"' + object '"'; //normally, we would do normal escaping here
}

function toJSON(object) :: Any -> string? {
  var type = typeof object;
  var ret :: string? = null<string>;

  if (type === "undefined" || type === "function" ||
      type === "unknown")
  {
    ret = null<string>;
  }
  else if (object === null) {
    ret = "null";
  }
  else if (type === "boolean") {
    ret = type ? "true" : "false"; //return object.toString();
  }
  else if (object.toJSON) { //TODO: this wont work
    ret = object.toJSON();
  }
  else if (isElement(object)) { //from "Object"
    ret = null<string>;
  }
  else {
    var results :: Array<string> = [];
    for (var property in object) {
      var value :: string? = toJSON(object[property]); //from "Object"
      if (value!==null<string>) //!(typeof value === "undefined"))
        results.push(escapeString(property) + ': ' + value);
    }

    ret = '{' + results.join(', ') + '}';
  }
  return ret;
}
*/