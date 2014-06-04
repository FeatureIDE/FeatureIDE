package com.sleepycat.je.cleaner;
public class Cleaner {
  Level detailedTraceLevel;
  /** 
 * Send trace messages to the java.util.logger. Don't rely on the logger
 * alone to conditionalize whether we send this message, we don't even want
 * to construct the message if the level is not enabled.
 */
  void trace(  Level level,  String action,  Node node,  long logLsn,  boolean completed,  boolean obsolete,  boolean dirtiedMigrated){
    new Cleaner_trace(this,level,action,node,logLsn,completed,obsolete,dirtiedMigrated).execute();
  }
  protected void hook90() throws DatabaseException {
    detailedTraceLevel=Tracer.parseLevel(env,EnvironmentParams.JE_LOGGING_LEVEL_CLEANER);
    original();
  }
  protected void hook91(  LN ln,  boolean obsolete,  boolean completed) throws DatabaseException {
    trace(detailedTraceLevel,CLEAN_PENDING_LN,ln,DbLsn.NULL_LSN,completed,obsolete,false);
    original(ln,obsolete,completed);
  }
  protected void hook92(  long lsn,  String cleanAction,  boolean obsolete,  boolean migrated,  boolean completed,  LN ln) throws DatabaseException {
    trace(detailedTraceLevel,cleanAction,ln,lsn,completed,obsolete,migrated);
    original(lsn,cleanAction,obsolete,migrated,completed,ln);
  }
  protected void hook93(  long lsn,  String cleanAction,  boolean obsolete,  boolean migrated,  boolean completed,  LN ln) throws DatabaseException {
    trace(detailedTraceLevel,cleanAction,ln,lsn,completed,obsolete,migrated);
    original(lsn,cleanAction,obsolete,migrated,completed,ln);
  }
@MethodObject static class Cleaner_trace {
    Cleaner_trace(    Cleaner _this,    Level level,    String action,    Node node,    long logLsn,    boolean completed,    boolean obsolete,    boolean dirtiedMigrated){
      this._this=_this;
      this.level=level;
      this.action=action;
      this.node=node;
      this.logLsn=logLsn;
      this.completed=completed;
      this.obsolete=obsolete;
      this.dirtiedMigrated=dirtiedMigrated;
    }
    void execute(){
    }
    protected Cleaner _this;
    protected Level level;
    protected String action;
    protected Node node;
    protected long logLsn;
    protected boolean completed;
    protected boolean obsolete;
    protected boolean dirtiedMigrated;
    protected Logger logger;
    protected StringBuffer sb;
  }
}
