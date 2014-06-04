package com.sleepycat.je.util;
import java.io.File;
import java.io.IOException;
import com.sleepycat.je.DatabaseException;
import com.sleepycat.je.config.EnvironmentParams;
import com.sleepycat.je.dbi.EnvironmentImpl;
import com.sleepycat.je.log.DumpFileReader;
import com.sleepycat.je.log.FileManager;
import com.sleepycat.je.log.PrintFileReader;
import com.sleepycat.je.log.StatsFileReader;
import com.sleepycat.je.tree.Key;
import com.sleepycat.je.utilint.CmdUtil;
import com.sleepycat.je.utilint.DbLsn;
import de.ovgu.cide.jakutil.*;
/** 
 * DbPrintLog is a debugging utility that dumps JE log files into a human
 * readable form.
 */
public class DbPrintLog {
  /** 
 * Dump a JE log into human readable form.
 */
  private void dump(  File envHome,  String entryTypes,  String txnIds,  long startLsn,  long endLsn,  boolean verbose,  boolean stats) throws IOException, DatabaseException {
    EnvironmentImpl env=CmdUtil.makeUtilityEnvironment(envHome,true);
    FileManager fileManager=env.getFileManager();
    fileManager.setIncludeDeletedFiles(true);
    int readBufferSize=env.getConfigManager().getInt(EnvironmentParams.LOG_ITERATOR_READ_SIZE);
    DumpFileReader reader=null;
    if (stats) {
      reader=new StatsFileReader(env,readBufferSize,startLsn,endLsn,entryTypes,txnIds,verbose);
    }
 else {
      reader=new PrintFileReader(env,readBufferSize,startLsn,endLsn,entryTypes,txnIds,verbose);
    }
    System.out.println("<DbPrintLog>");
    while (reader.readNextEntry()) {
    }
    reader.summarize();
    System.out.println("</DbPrintLog>");
    env.close();
  }
  /** 
 * Main
 */
  public static void main(  String[] argv){
    try {
      int whichArg=0;
      String entryTypes=null;
      String txnIds=null;
      long startLsn=DbLsn.NULL_LSN;
      long endLsn=DbLsn.NULL_LSN;
      boolean verbose=true;
      boolean stats=false;
      File envHome=new File(".");
      Key.DUMP_BINARY=true;
      while (whichArg < argv.length) {
        String nextArg=argv[whichArg];
        if (nextArg.equals("-h")) {
          whichArg++;
          envHome=new File(CmdUtil.getArg(argv,whichArg));
        }
 else         if (nextArg.equals("-ty")) {
          whichArg++;
          entryTypes=CmdUtil.getArg(argv,whichArg);
        }
 else         if (nextArg.equals("-tx")) {
          whichArg++;
          txnIds=CmdUtil.getArg(argv,whichArg);
        }
 else         if (nextArg.equals("-s")) {
          whichArg++;
          long startFileNum=CmdUtil.readLongNumber(CmdUtil.getArg(argv,whichArg));
          startLsn=DbLsn.makeLsn(startFileNum,0);
        }
 else         if (nextArg.equals("-e")) {
          whichArg++;
          long endFileNum=CmdUtil.readLongNumber(CmdUtil.getArg(argv,whichArg));
          endLsn=DbLsn.makeLsn(endFileNum,0);
        }
 else         if (nextArg.equals("-k")) {
          whichArg++;
          String dumpType=CmdUtil.getArg(argv,whichArg);
          if (dumpType.equalsIgnoreCase("text")) {
            Key.DUMP_BINARY=false;
          }
        }
 else         if (nextArg.equals("-q")) {
          whichArg++;
          verbose=false;
        }
 else         if (nextArg.equals("-S")) {
          whichArg++;
          stats=true;
        }
 else {
          System.err.println(nextArg + " is not a supported option.");
          usage();
          System.exit(-1);
        }
        whichArg++;
      }
      DbPrintLog printer=new DbPrintLog();
      printer.dump(envHome,entryTypes,txnIds,startLsn,endLsn,verbose,stats);
    }
 catch (    Throwable e) {
      e.printStackTrace();
      System.out.println(e.getMessage());
      usage();
      System.exit(1);
    }
  }
  private static void usage(){
    System.out.println("Usage: " + CmdUtil.getJavaCommand(DbPrintLog.class));
    System.out.println(" -h  <envHomeDir>");
    System.out.println(" -e  <end file number, in hex>");
    System.out.println(" -k  <binary|text> (format for dumping the key)");
    System.out.println(" -s  <start file number, in hex>");
    System.out.println(" -tx <targetted txn ids, comma separated>");
    System.out.println(" -ty <targetted entry types, comma separated>");
    System.out.println(" -S  show Summary of log entries");
    System.out.println(" -q  if specified, concise version is printed");
    System.out.println("     Default is verbose version.)");
    System.out.println("All arguments are optional");
  }
}
