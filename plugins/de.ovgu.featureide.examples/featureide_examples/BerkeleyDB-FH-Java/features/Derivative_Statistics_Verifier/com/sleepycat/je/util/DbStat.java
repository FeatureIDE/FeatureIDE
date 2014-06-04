package com.sleepycat.je.util;
import java.io.File;
import java.io.PrintStream;
import java.util.logging.Level;
import com.sleepycat.je.Database;
import com.sleepycat.je.DatabaseConfig;
import com.sleepycat.je.DatabaseException;
import com.sleepycat.je.DatabaseStats;
import com.sleepycat.je.DbInternal;
import com.sleepycat.je.Environment;
import com.sleepycat.je.JEVersion;
import com.sleepycat.je.StatsConfig;
import com.sleepycat.je.utilint.CmdUtil;
import com.sleepycat.je.utilint.Tracer;
import de.ovgu.cide.jakutil.*;
public class DbStat extends DbVerify {
  private String usageString="usage: " + CmdUtil.getJavaCommand(DbStat.class) + "\n"+ "               [-V] -s database -h dbEnvHome [-v progressInterval]\n";
  private int progressInterval=0;
  static public void main(  String argv[]) throws DatabaseException {
    DbStat stat=new DbStat();
    stat.parseArgs(argv);
    int ret=0;
    try {
      if (!stat.stats(System.err)) {
        ret=1;
      }
    }
 catch (    Throwable T) {
      ret=1;
      T.printStackTrace(System.err);
    }
    try {
      stat.env.close();
    }
 catch (    Throwable ignored) {
    }
    System.exit(ret);
  }
  protected DbStat(){
  }
  public DbStat(  Environment env,  String dbName){
    super(env,dbName,false);
  }
  protected void printUsage(  String msg){
    System.err.println(msg);
    System.err.println(usageString);
    System.exit(-1);
  }
  protected void parseArgs(  String argv[]){
    int argc=0;
    int nArgs=argv.length;
    while (argc < nArgs) {
      String thisArg=argv[argc++];
      if (thisArg.equals("-V")) {
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
 else       if (thisArg.equals("-s")) {
        if (argc < nArgs) {
          dbName=argv[argc++];
        }
 else {
          printUsage("-s requires an argument");
        }
      }
 else       if (thisArg.equals("-v")) {
        if (argc < nArgs) {
          progressInterval=Integer.parseInt(argv[argc++]);
          if (progressInterval <= 0) {
            printUsage("-v requires a positive argument");
          }
        }
 else {
          printUsage("-v requires an argument");
        }
      }
    }
    if (envHome == null) {
      printUsage("-h is a required argument");
    }
    if (dbName == null) {
      printUsage("-s is a required argument");
    }
  }
  public boolean stats(  PrintStream out) throws DatabaseException {
    try {
      openEnv();
      this.hook850();
      DatabaseConfig dbConfig=new DatabaseConfig();
      dbConfig.setReadOnly(true);
      dbConfig.setAllowCreate(false);
      DbInternal.setUseExistingConfig(dbConfig,true);
      Database db=env.openDatabase(null,dbName,dbConfig);
      StatsConfig statsConfig=new StatsConfig();
      if (progressInterval > 0) {
        statsConfig.setShowProgressInterval(progressInterval);
        statsConfig.setShowProgressStream(out);
      }
      DatabaseStats stats=db.getStats(statsConfig);
      out.println(stats);
      db.close();
      this.hook849();
    }
 catch (    DatabaseException DE) {
      return false;
    }
    return true;
  }
  protected void hook849() throws DatabaseException {
  }
  protected void hook850() throws DatabaseException {
  }
}
