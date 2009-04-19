function() :: (->) {

  var obj = {
    x: 0,
    inc : function() :: [rec self . { x :: int, 
                                      inc :: ([self] -> int) }] -> int {
      this.x = this.x + 1;
      return this.x;
    }
  };

  obj.inc();

  obj.inc();
  

} @@ succeeds;


function() :: (->) {

  var obj = {
    x: 0,
    inc : function() :: [rec self . { x :: int, 
                                      inc :: ([self] -> int) }] -> int {
      this.x = this.x + 1;
      return this.x;
    }
  };

  var y = obj.inc; // just naming it is fine

  obj.inc();
  

} @@ succeeds;


function() :: (->) {

  var obj = {
    x: 0,
    inc : function() :: [rec self . { x :: int, 
                                      inc :: ([self] -> int) }] -> int {
      this.x = this.x + 1;
      return this.x;
    }
  };

  var y = obj.inc;

  obj.inc();
  y(); // calling it fails because this is wrong
  

} @@ fails;
