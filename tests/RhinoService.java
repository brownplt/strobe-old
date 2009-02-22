import java.io.*;
import org.mozilla.javascript.*;

import org.mozilla.javascript.tools.shell.*;

/* Read from stdin a number, followed by a newline, followed by that many bytes
   If this first line is blank, then the service exits.
   Run those bytes as javascript code.
   Output a number, followed by a newline, followed by that many bytes, representing
   the output of running that code, which is whatever the code output, including
   errors.
   Repeat.
*/

public class RhinoService
{
  final static String SENTINEL = ":%:%:";
  public static void main(String[] args) {
    //initialize pJS, augmented with Rhino shell
    Global g = new Global();
    ShellContextFactory cf = new ShellContextFactory();
    g.init(cf);
    Context cx = cf.enterContext();
    //note: doesn't define Rhino shell vars like print.
    Scriptable scope = g; //cx.initStandardObjects();
    try {
      boolean done=false;
      int scriptNumber = 0;
      InputStreamReader isr = new InputStreamReader(System.in);
      BufferedReader rdr = new BufferedReader(isr);
      while (!done) {
        String l = rdr.readLine();
        if (l==null || l.length() == 0) //end of input
          break;
                   
        int numBytes = 0;
        try {
          numBytes = Integer.parseInt(l);
        }
        catch (NumberFormatException e) {
          break;
        }
                    
        String sourceName = "<cmd " + (scriptNumber++) + ">";

        char[] script = new char[numBytes];
        int bytesRead = 0, offset = 0;
        while (offset != numBytes) {
          bytesRead = rdr.read(script, offset, numBytes - offset);
          if (bytesRead == -1) { //premature EOF
            done=true;
            break;
          }
          offset += bytesRead;
        }
        if (done) break;

        //args: (scope, script, sourcename, line number, security context)
        String toOutput = "";
        try {
          Object res = cx.evaluateString(scope, new String(script), 
                                         sourceName, 1, null);
          String sres = res.toString();
          toOutput = sres;
        }
        catch (Exception e) {
          toOutput = e.toString();
        }
        //print a sentinel in case the script had any output of its own
        System.out.println("\n" + SENTINEL + "\n" + (toOutput.length()+1) + "\n" + toOutput);
      } 
    }
    catch (IOException e) {
      System.exit(1);
    }
  }
}