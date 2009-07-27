relations {
  HTMLElement: <: Element:
}

expressions {

  succeed function(doc) :: HTMLDocument: -> String {
    return doc.title;
  };

  succeed function() :: (-> Undefined) {
    document.title = "this should work";
  };

  fail function() :: (-> Undefined) {
    document.title = 234234;
  };

  succeed function() :: (-> Undefined) {
    document.write("Calling a method succeeds.");
  };


  fail function() :: (-> Undefined) {
    // This code may work in the browser.  However, it is always safe to reject
    // code.
    var m = document.write;
    m("Failure because this is wrong.");
  };

  succeed  function(element) :: HTMLElement: -> { left:: Int, top:: Int } {
    var valueT = 0, valueL = 0;
    do {
      valueT += element.offsetTop || 0;
      valueL += element.offsetLeft || 0;
      element = element.offsetParent;
    } while (element);
    return { left: valueL, top: valueT };
  }

}
