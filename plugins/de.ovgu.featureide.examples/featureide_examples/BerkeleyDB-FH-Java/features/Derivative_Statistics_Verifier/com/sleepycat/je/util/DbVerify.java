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
import com.sleepycat.je.EnvironmentConfig;
import com.sleepycat.je.JEVersion;
import com.sleepycat.je.VerifyConfig;
import com.sleepycat.je.cleaner.VerifyUtils;
import com.sleepycat.je.dbi.DatabaseImpl;
import com.sleepycat.je.dbi.EnvironmentImpl;
import com.sleepycat.je.utilint.CmdUtil;
import com.sleepycat.je.utilint.Tracer;
import de.ovgu.cide.jakutil.*;
public class DbVerify {
  private static final String usageString="usage: " + CmdUtil.getJavaCommand(DbVerify.class) + "\n"+ "       -h <dir>             # environment home directory\n"+ "       [-q ]                # quiet, exit with success or failure\n"+ "       [-s <databaseName> ] # database to verify\n"+ "       [-v <interval>]      # progress notification interval\n"+ "       [-V]                 # print JE version number";
  protected File envHome=null;
  protected Environment env;
  protected String dbName=null;
  protected boolean quiet=false;
  protected boolean checkLsns=false;
  private int progressInterval=0;
  static public void main(  String argv[]) throws DatabaseException {
    DbVerify verifier=new DbVerify();
    verifier.parseArgs(argv);
    boolean ret=false;
    try {
      ret=verifier.verify(System.err);
    }
 catch (    Throwable T) {
      if (!verifier.quiet) {
        T.printStackTrace(System.err);
      }
    }
 finally {
      verifier.closeEnv();
      if ((!verifier.quiet) || (verifier.progressInterval > 0)) {
        System.err.println("Exit status = " + ret);
      }
      System.exit(ret ? 0 : -1);
    }
  }
  protected DbVerify(){
  }
  public DbVerify(  Environment env,  String dbName,  boolean quiet){
    this.env=env;
    this.dbName=dbName;
    this.quiet=quiet;
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
      if (thisArg.equals("-q")) {
        quiet=true;
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
 else       if (thisArg.equals("-c")) {
        checkLsns=true;
      }
    }
    if (envHome == null) {
      printUsage("-h is a required argument");
    }
    if (dbName == null) {
      printUsage("-s is a required argument");
    }
  }
  protected void openEnv() throws DatabaseException {
    if (env == null) {
      EnvironmentConfig envConfig=new EnvironmentConfig();
      envConfig.setReadOnly(true);
      env=new Environment(envHome,envConfig);
    }
  }
  void closeEnv() throws DatabaseException {
    try {
      if (env != null) {
        env.close();
      }
    }
  finally {
      env=null;
    }
  }
  public boolean verify(  PrintStream out) throws DatabaseException {
    boolean ret=true;
    try {
      VerifyConfig verifyConfig=new VerifyConfig();
      verifyConfig.setPrintInfo(!quiet);
      if (progressInterval > 0) {
        verifyConfig.setShowProgressInterval(progressInterval);
        verifyConfig.setShowProgressStream(out);
      }
      openEnv();
      EnvironmentImpl envImpl=DbInternal.envGetEnvironmentImpl(env);
      this.hook851(envImpl);
      DatabaseConfig dbConfig=new DatabaseConfig();
      dbConfig.setReadOnly(true);
      dbConfig.setAllowCreate(false);
      DbInternal.setUseExistingConfig(dbConfig,true);
      Database db=env.openDatabase(null,dbName,dbConfig);
      try {
        if (checkLsns) {
          System.out.println("Checking obsolete offsets ...");
          VerifyUtils.checkLsns(db);
        }
 else {
          DatabaseImpl dbImpl=DbInternal.dbGetDatabaseImpl(db);
          DatabaseStats stats=dbImpl.getEmptyStats();
          ret=dbImpl.verify(verifyConfig,stats);
          if (verifyConfig.getPrintInfo()) {
            out.println(stats);
          }
        }
      }
  finally {
        if (db != null) {
          db.close();
        }
        this.hook852(envImpl);
      }
      closeEnv();
    }
 catch (    DatabaseException DE) {
      ret=false;
      try {
        closeEnv();
      }
 catch (      Throwable ignored) {
      }
      throw DE;
    }
    return ret;
  }
  protected void hook851(  EnvironmentImpl envImpl) throws DatabaseException {
  }
  protected void hook852(  EnvironmentImpl envImpl) throws DatabaseException {
  }
}
