package com.sleepycat.je.util;
import java.io.File;
import java.io.PrintStream;
import java.util.Arrays;
import java.util.Iterator;
import java.util.Map;
import java.util.SortedMap;
import com.sleepycat.je.DatabaseException;
import com.sleepycat.je.DbInternal;
import com.sleepycat.je.Environment;
import com.sleepycat.je.EnvironmentConfig;
import com.sleepycat.je.JEVersion;
import com.sleepycat.je.cleaner.FileSummary;
import com.sleepycat.je.cleaner.UtilizationProfile;
import com.sleepycat.je.dbi.EnvironmentImpl;
import com.sleepycat.je.utilint.CmdUtil;
import de.ovgu.cide.jakutil.*;
public class DbSpace {
  private static final String USAGE="usage: " + CmdUtil.getJavaCommand(DbSpace.class) + "\n"+ "       -h <dir> # environment home directory\n"+ "       [-q]     # quiet, print grand totals only\n"+ "       [-u]     # sort by utilization\n"+ "       [-d]     # dump file summary details\n"+ "       [-V]     # print JE version number";
  public static void main(  String argv[]) throws DatabaseException {
    DbSpace space=new DbSpace();
    space.parseArgs(argv);
    EnvironmentConfig envConfig=new EnvironmentConfig();
    envConfig.setReadOnly(true);
    Environment env=new Environment(space.envHome,envConfig);
    space.envImpl=DbInternal.envGetEnvironmentImpl(env);
    try {
      space.print(System.out);
      System.exit(0);
    }
 catch (    Throwable e) {
      e.printStackTrace(System.err);
      System.exit(1);
    }
 finally {
      try {
        env.close();
      }
 catch (      Throwable e) {
        e.printStackTrace(System.err);
        System.exit(1);
      }
    }
  }
  private File envHome=null;
  private EnvironmentImpl envImpl;
  private boolean quiet=false;
  private boolean sorted=false;
  private boolean details=false;
  private DbSpace(){
  }
  public DbSpace(  Environment env,  boolean quiet,  boolean details,  boolean sorted){
    this(DbInternal.envGetEnvironmentImpl(env),quiet,details,sorted);
  }
  public DbSpace(  EnvironmentImpl envImpl,  boolean quiet,  boolean details,  boolean sorted){
    this.envImpl=envImpl;
    this.quiet=quiet;
    this.details=details;
    this.sorted=sorted;
  }
  private void printUsage(  String msg){
    if (msg != null) {
      System.err.println(msg);
    }
    System.err.println(USAGE);
    System.exit(-1);
  }
  private void parseArgs(  String argv[]){
    int argc=0;
    int nArgs=argv.length;
    if (nArgs == 0) {
      printUsage(null);
      System.exit(0);
    }
    while (argc < nArgs) {
      String thisArg=argv[argc++];
      if (thisArg.equals("-q")) {
        quiet=true;
      }
 else       if (thisArg.equals("-u")) {
        sorted=true;
      }
 else       if (thisArg.equals("-d")) {
        details=true;
      }
 else       if (thisArg.equals("-V")) {
        System.out.println(JEVersion.CURRENT_VERSION);
        System.exit(0);
      }
 else       if (thisArg.equals("-h")) {
        if (argc < nArgs) {
          envHome=new File(argv[argc++]);
        }
 else {
          printUsage("-h requires an argument");
        }
      }
    }
    if (envHome == null) {
      printUsage("-h is a required argument");
    }
  }
  public void print(  PrintStream out) throws DatabaseException {
    UtilizationProfile profile=envImpl.getUtilizationProfile();
    SortedMap map=profile.getFileSummaryMap(false);
    int fileIndex=0;
    Summary totals=new Summary();
    Summary[] summaries=null;
    if (!quiet) {
      summaries=new Summary[map.size()];
    }
    Iterator iter=map.entrySet().iterator();
    while (iter.hasNext()) {
      Map.Entry entry=(Map.Entry)iter.next();
      Long fileNum=(Long)entry.getKey();
      FileSummary fs=(FileSummary)entry.getValue();
      Summary summary=new Summary(fileNum,fs);
      if (summaries != null) {
        summaries[fileIndex]=summary;
      }
      if (details) {
        out.println("File 0x" + Long.toHexString(fileNum.longValue()) + ": "+ fs);
      }
      totals.add(summary);
      fileIndex+=1;
    }
    if (details) {
      out.println();
    }
    out.println(Summary.HEADER);
    if (summaries != null) {
      if (sorted) {
        Arrays.sort(summaries);
      }
      for (int i=0; i < summaries.length; i+=1) {
        summaries[i].print(out);
      }
    }
    totals.print(out);
  }
private static class Summary implements Comparable {
    static final String HEADER="  File    Size (KB)  % Used\n" + "--------  ---------  ------";
    Long fileNum;
    long totalSize;
    long obsoleteSize;
    Summary(){
    }
    Summary(    Long fileNum,    FileSummary summary) throws DatabaseException {
      this.fileNum=fileNum;
      totalSize=summary.totalSize;
      obsoleteSize=summary.getObsoleteSize();
    }
    public int compareTo(    Object other){
      Summary o=(Summary)other;
      return utilization() - o.utilization();
    }
    void add(    Summary o){
      totalSize+=o.totalSize;
      obsoleteSize+=o.obsoleteSize;
    }
    void print(    PrintStream out){
      if (fileNum != null) {
        pad(out,Long.toHexString(fileNum.longValue()),8,'0');
      }
 else {
        out.print(" TOTALS ");
      }
      int kb=(int)(totalSize / 1024);
      int util=utilization();
      out.print("  ");
      pad(out,Integer.toString(kb),9,' ');
      out.print("     ");
      pad(out,Integer.toString(util),3,' ');
      out.println();
    }
    int utilization(){
      return UtilizationProfile.utilization(obsoleteSize,totalSize);
    }
    private void pad(    PrintStream out,    String val,    int digits,    char padChar){
      int padSize=digits - val.length();
      for (int i=0; i < padSize; i+=1) {
        out.print(padChar);
      }
      out.print(val);
    }
  }
}
