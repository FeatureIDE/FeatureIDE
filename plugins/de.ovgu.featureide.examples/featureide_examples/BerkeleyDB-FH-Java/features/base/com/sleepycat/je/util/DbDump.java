package com.sleepycat.je.util;
import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.PrintStream;
import java.util.Iterator;
import java.util.List;
import java.util.logging.Level;
import com.sleepycat.je.Cursor;
import com.sleepycat.je.Database;
import com.sleepycat.je.DatabaseConfig;
import com.sleepycat.je.DatabaseEntry;
import com.sleepycat.je.DatabaseException;
import com.sleepycat.je.DbInternal;
import com.sleepycat.je.Environment;
import com.sleepycat.je.EnvironmentConfig;
import com.sleepycat.je.JEVersion;
import com.sleepycat.je.LockMode;
import com.sleepycat.je.OperationStatus;
import com.sleepycat.je.config.EnvironmentParams;
import com.sleepycat.je.utilint.CmdUtil;
import com.sleepycat.je.utilint.DbScavenger;
import com.sleepycat.je.utilint.Tracer;
import de.ovgu.cide.jakutil.*;
public class DbDump {
  private static final int VERSION=3;
  protected File envHome=null;
  protected Environment env;
  protected String dbName=null;
  protected boolean formatUsingPrintable;
  private boolean dupSort;
  private String outputFileName=null;
  protected String outputDirectory=null;
  protected PrintStream outputFile=null;
  protected boolean doScavengerRun=false;
  protected boolean doAggressiveScavengerRun=false;
  protected boolean verbose=false;
  private static final String usageString="usage: " + CmdUtil.getJavaCommand(DbDump.class) + "\n"+ "  -h <dir> # environment home directory\n"+ "  [-f <fileName>]     # output file, for non -rR dumps\n"+ "  [-l]                # list databases in the environment\n"+ "  [-p]                # output printable characters\n"+ "  [-r]                # salvage mode\n"+ "  [-R]                # aggressive salvage mode\n"+ "  [-d] <directory>    # directory for *.dump files (salvage mode)\n"+ "  [-s <databaseName>] # database to dump\n"+ "  [-v]                # verbose in salvage mode\n"+ "  [-V]                # print JE version number\n";
  private DbDump(){
  }
  public DbDump(  Environment env,  String dbName,  PrintStream outputFile,  String outputDirectory,  boolean formatUsingPrintable){
    try {
      this.envHome=env.getHome();
    }
 catch (    DatabaseException e) {
      IllegalArgumentException iae=new IllegalArgumentException();
      iae.initCause(e);
      throw iae;
    }
    this.env=env;
    this.dbName=dbName;
    this.outputFile=outputFile;
    this.outputDirectory=outputDirectory;
    this.formatUsingPrintable=formatUsingPrintable;
  }
  public static void main(  String argv[]) throws DatabaseException, IOException {
    DbDump dumper=new DbDump();
    boolean listDbs=dumper.parseArgs(argv);
    if (dumper.doScavengerRun) {
      dumper.openEnv(false);
      dumper=new DbScavenger(dumper.env,dumper.outputFile,dumper.outputDirectory,dumper.formatUsingPrintable,dumper.doAggressiveScavengerRun,dumper.verbose);
      ((DbScavenger)dumper).setDumpCorruptedBounds(true);
    }
    if (listDbs) {
      dumper.listDbs();
      System.exit(0);
    }
    try {
      dumper.dump();
    }
 catch (    Throwable T) {
      T.printStackTrace();
    }
 finally {
      dumper.env.close();
      if (dumper.outputFile != null && dumper.outputFile != System.out) {
        dumper.outputFile.close();
      }
    }
  }
  private void listDbs() throws DatabaseException {
    openEnv(true);
    List dbNames=env.getDatabaseNames();
    Iterator iter=dbNames.iterator();
    while (iter.hasNext()) {
      String name=(String)iter.next();
      System.out.println(name);
    }
  }
  protected void printUsage(  String msg){
    System.err.println(msg);
    System.err.println(usageString);
    System.exit(-1);
  }
  protected boolean parseArgs(  String argv[]) throws IOException {
    int argc=0;
    int nArgs=argv.length;
    boolean listDbs=false;
    while (argc < nArgs) {
      String thisArg=argv[argc++];
      if (thisArg.equals("-p")) {
        formatUsingPrintable=true;
      }
 else       if (thisArg.equals("-V")) {
        System.out.println(JEVersion.CURRENT_VERSION);
        System.exit(0);
      }
 else       if (thisArg.equals("-l")) {
        listDbs=true;
      }
 else       if (thisArg.equals("-r")) {
        doScavengerRun=true;
      }
 else       if (thisArg.equals("-R")) {
        doScavengerRun=true;
        doAggressiveScavengerRun=true;
      }
 else       if (thisArg.equals("-f")) {
        if (argc < nArgs) {
          outputFileName=argv[argc++];
        }
 else {
          printUsage("-f requires an argument");
        }
      }
 else       if (thisArg.equals("-h")) {
        if (argc < nArgs) {
          String envDir=argv[argc++];
          envHome=new File(envDir);
        }
 else {
          printUsage("-h requires an argument");
        }
      }
 else       if (thisArg.equals("-d")) {
        if (argc < nArgs) {
          outputDirectory=argv[argc++];
        }
 else {
          printUsage("-d requires an argument");
        }
      }
 else       if (thisArg.equals("-s")) {
        if (argc < nArgs) {
          dbName=argv[argc++];
        }
 else {
          printUsage("-s requires an argument");
        }
      }
 else       if (thisArg.equals("-v")) {
        verbose=true;
      }
 else {
        printUsage(thisArg + " is not a valid option.");
      }
    }
    if (envHome == null) {
      printUsage("-h is a required argument");
    }
    if (!listDbs && !doScavengerRun) {
      if (dbName == null) {
        printUsage("Must supply a database name if -l not supplied.");
      }
    }
    if (outputFileName == null) {
      outputFile=System.out;
    }
 else {
      outputFile=new PrintStream(new FileOutputStream(outputFileName));
    }
    return listDbs;
  }
  protected void openEnv(  boolean doRecovery) throws DatabaseException {
    if (env == null) {
      EnvironmentConfig envConfiguration=new EnvironmentConfig();
      envConfiguration.setReadOnly(true);
      envConfiguration.setConfigParam(EnvironmentParams.ENV_RECOVERY.getName(),doRecovery ? "true" : "false");
      env=new Environment(envHome,envConfiguration);
    }
  }
  public void dump() throws IOException, DatabaseException {
    openEnv(true);
    this.hook834();
    DatabaseEntry foundKey=new DatabaseEntry();
    DatabaseEntry foundData=new DatabaseEntry();
    DatabaseConfig dbConfig=new DatabaseConfig();
    dbConfig.setReadOnly(true);
    DbInternal.setUseExistingConfig(dbConfig,true);
    Database db=env.openDatabase(null,dbName,dbConfig);
    dupSort=db.getConfig().getSortedDuplicates();
    printHeader(outputFile,dupSort,formatUsingPrintable);
    Cursor cursor=db.openCursor(null,null);
    while (cursor.getNext(foundKey,foundData,LockMode.DEFAULT) == OperationStatus.SUCCESS) {
      dumpOne(outputFile,foundKey.getData(),formatUsingPrintable);
      dumpOne(outputFile,foundData.getData(),formatUsingPrintable);
    }
    cursor.close();
    db.close();
    outputFile.println("DATA=END");
  }
  protected void printHeader(  PrintStream o,  boolean dupSort,  boolean formatUsingPrintable){
    o.println("VERSION=" + VERSION);
    if (formatUsingPrintable) {
      o.println("format=print");
    }
 else {
      o.println("format=bytevalue");
    }
    o.println("type=btree");
    o.println("dupsort=" + (dupSort ? "1" : "0"));
    o.println("HEADER=END");
  }
  protected void dumpOne(  PrintStream o,  byte[] ba,  boolean formatUsingPrintable){
    StringBuffer sb=new StringBuffer();
    sb.append(' ');
    CmdUtil.formatEntry(sb,ba,formatUsingPrintable);
    o.println(sb.toString());
  }
  protected void hook834() throws IOException, DatabaseException {
  }
}
