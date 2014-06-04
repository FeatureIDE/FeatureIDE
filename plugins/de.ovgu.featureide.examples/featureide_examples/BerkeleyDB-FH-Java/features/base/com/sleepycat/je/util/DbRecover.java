package com.sleepycat.je.util;
import java.io.File;
import com.sleepycat.je.dbi.EnvironmentImpl;
import com.sleepycat.je.utilint.CmdUtil;
import de.ovgu.cide.jakutil.*;
/** 
 * DbRecover is a utility that allows the user to resume use of the environment
 * from a given time point. Not for general use yet!
 */
public class DbRecover {
  public static void main(  String[] argv){
    try {
      int whichArg=0;
      boolean seenFile=false;
      boolean seenOffset=false;
      long truncateFileNum=-1;
      long truncateOffset=-1;
      File envHome=new File(".");
      while (whichArg < argv.length) {
        String nextArg=argv[whichArg];
        if (nextArg.equals("-h")) {
          whichArg++;
          envHome=new File(CmdUtil.getArg(argv,whichArg));
        }
 else         if (nextArg.equals("-f")) {
          whichArg++;
          truncateFileNum=CmdUtil.readLongNumber(CmdUtil.getArg(argv,whichArg));
          seenFile=true;
        }
 else         if (nextArg.equals("-o")) {
          whichArg++;
          truncateOffset=CmdUtil.readLongNumber(CmdUtil.getArg(argv,whichArg));
          seenOffset=true;
        }
 else {
          throw new IllegalArgumentException(nextArg + " is not a supported option.");
        }
        whichArg++;
      }
      if ((!seenFile) || (!seenOffset)) {
        usage();
        System.exit(1);
      }
      EnvironmentImpl env=CmdUtil.makeUtilityEnvironment(envHome,false);
      env.getFileManager().truncateLog(truncateFileNum,truncateOffset);
      env.close();
    }
 catch (    Exception e) {
      e.printStackTrace();
      System.out.println(e.getMessage());
      usage();
      System.exit(1);
    }
  }
  private static void usage(){
    System.out.println("Usage: " + CmdUtil.getJavaCommand(DbRecover.class));
    System.out.println("                 -h <environment home>");
    System.out.println("(optional)");
    System.out.println("                 -f <file number, in hex>");
    System.out.println("                 -o <offset, in hex>");
    System.out.println("Log file is truncated at position starting at" + " and inclusive of the offset. Beware, not " + " for general purpose use yet!");
  }
}
