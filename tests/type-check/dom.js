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
  }
}
