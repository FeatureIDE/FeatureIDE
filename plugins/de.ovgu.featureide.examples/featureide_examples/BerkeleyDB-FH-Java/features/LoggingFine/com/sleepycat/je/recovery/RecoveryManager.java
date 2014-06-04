package com.sleepycat.je.recovery;
public class RecoveryManager {
  /** 
 * Log trace information about root deletions, called by INCompressor and
 * recovery.
 */
  public static void traceRootDeletion(  Level level,  DatabaseImpl database){
    new RecoveryManager_traceRootDeletion(level,database).execute();
  }
  protected void hook557(  DatabaseImpl db) throws DatabaseException {
    traceRootDeletion(Level.FINE,db);
    original(db);
  }
@MethodObject static class RecoveryManager_traceRootDeletion {
    RecoveryManager_traceRootDeletion(    Level level,    DatabaseImpl database){
      this.level=level;
      this.database=database;
    }
    void execute(){
    }
    protected Level level;
    protected DatabaseImpl database;
    protected Logger logger;
    protected StringBuffer sb;
  }
}
