import java.io.*;
import org.mozilla.javascript.*;

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
    /*public static Object runString(String script, String sourceName) 
    {
        return cx.evaluateString(scope, script, sourceName, 1, null);
        }*/
    public static void main(String[] args) {
        //initialize pJS:
        ContextFactory cf = new ContextFactory();
        Context cx = cf.enterContext();
        //note: doesn't define Rhino shell vars like print.
        Scriptable scope = cx.initStandardObjects();

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
                //System.out.println("Reading " + numBytes + " bytes...");

                char[] script = new char[numBytes];
                int bytesRead = 0, offset = 0;
                while (offset != numBytes) {
                    bytesRead = isr.read(script, offset, numBytes - offset);
                    if (bytesRead == -1) { //premature EOF
                        done=true;
                        break;
                    }
                    offset += bytesRead;
                }
                if (done) break;

                //args: (scope, script, sourcename, line number, security context)
                try {
                    Object res = cx.evaluateString(scope, new String(script), sourceName, 1, null);
                    String sres = res.toString();
                    System.out.println((sres.length()+1) + "\n" + sres);
                }
                catch (Exception e) {
                    System.out.println(e);
                }

            } 
        }
        catch (IOException e) {
            System.exit(1);
        }
    }
}