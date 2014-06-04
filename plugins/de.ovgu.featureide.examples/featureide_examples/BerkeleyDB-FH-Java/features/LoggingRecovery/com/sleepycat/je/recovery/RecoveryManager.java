package com.sleepycat.je.recovery;
public class RecoveryManager {
  /** 
 * Send trace messages to the java.util.logger. Don't rely on the logger
 * alone to conditionalize whether we send this message, we don't even want
 * to construct the message if the level is not enabled.
 */
  private void traceINDeleteReplay(  long nodeId,  long logLsn,  boolean found,  boolean deleted,  int index,  boolean isDuplicate){
    new RecoveryManager_traceINDeleteReplay(this,nodeId,logLsn,found,deleted,index,isDuplicate).execute();
  }
  protected static void hook555(  Level traceLevel,  DatabaseImpl db,  TreeLocation location,  LN lnFromLog,  long logLsn,  long abortLsn,  boolean found,  boolean replaced,  boolean success) throws DatabaseException {
  }
  protected void hook578(  EnvironmentImpl env) throws DatabaseException {
    detailedTraceLevel=Tracer.parseLevel(env,EnvironmentParams.JE_LOGGING_LEVEL_RECOVERY);
    original(env);
  }
  protected void hook579(  long nodeId,  boolean containsDuplicates,  long logLsn,  boolean found,  boolean deleted,  SearchResult result) throws DatabaseException {
    traceINDeleteReplay(nodeId,logLsn,found,deleted,result.index,containsDuplicates);
    original(nodeId,containsDuplicates,logLsn,found,deleted,result);
  }
  protected void hook580(  DatabaseImpl db,  IN inFromLog,  long lsn,  boolean success,  RootUpdater rootUpdater) throws DatabaseException {
    trace(detailedTraceLevel,db,TRACE_ROOT_REPLACE,success,inFromLog,lsn,null,true,rootUpdater.getReplaced(),rootUpdater.getInserted(),rootUpdater.getOriginalLsn(),DbLsn.NULL_LSN,-1);
    original(db,inFromLog,lsn,success,rootUpdater);
  }
  protected void hook581(  DatabaseImpl db,  DIN inFromLog,  long lsn,  boolean found,  boolean inserted,  boolean replaced,  long origLsn,  IN parent,  int index,  boolean success) throws DatabaseException {
    trace(detailedTraceLevel,db,TRACE_DUP_ROOT_REPLACE,success,inFromLog,lsn,parent,found,replaced,inserted,origLsn,DbLsn.NULL_LSN,index);
    original(db,inFromLog,lsn,found,inserted,replaced,origLsn,parent,index,success);
  }
  protected void hook582(  DatabaseImpl db,  IN inFromLog,  long logLsn,  boolean inserted,  boolean replaced,  long origLsn,  boolean success,  SearchResult result) throws DatabaseException {
    trace(detailedTraceLevel,db,TRACE_IN_REPLACE,success,inFromLog,logLsn,result.parent,result.exactParentFound,replaced,inserted,origLsn,DbLsn.NULL_LSN,result.index);
    original(db,inFromLog,logLsn,inserted,replaced,origLsn,success,result);
  }
  protected void hook583(  DatabaseImpl db,  TreeLocation location,  LN lnFromLog,  long logLsn,  boolean found,  boolean replaced,  boolean inserted,  boolean success) throws DatabaseException {
    trace(detailedTraceLevel,db,TRACE_LN_REDO,success,lnFromLog,logLsn,location.bin,found,replaced,inserted,location.childLsn,DbLsn.NULL_LSN,location.index);
    original(db,location,lnFromLog,logLsn,found,replaced,inserted,success);
  }
  protected static void hook584(  Level traceLevel,  DatabaseImpl db,  TreeLocation location,  LN lnFromLog,  byte[] mainKey,  byte[] dupKey,  long logLsn,  long abortLsn,  boolean abortKnownDeleted,  RecoveryInfo info,  boolean splitsAllowed,  boolean found,  boolean replaced,  boolean success) throws DatabaseException {
    try {
      original(traceLevel,db,location,lnFromLog,mainKey,dupKey,logLsn,abortLsn,abortKnownDeleted,info,splitsAllowed,found,replaced,success);
    }
  finally {
      hook555(traceLevel,db,location,lnFromLog,logLsn,abortLsn,found,replaced,success);
    }
  }
@MethodObject static class RecoveryManager_traceINDeleteReplay {
    RecoveryManager_traceINDeleteReplay(    RecoveryManager _this,    long nodeId,    long logLsn,    boolean found,    boolean deleted,    int index,    boolean isDuplicate){
      this._this=_this;
      this.nodeId=nodeId;
      this.logLsn=logLsn;
      this.found=found;
      this.deleted=deleted;
      this.index=index;
      this.isDuplicate=isDuplicate;
    }
    void execute(){
    }
    protected RecoveryManager _this;
    protected long nodeId;
    protected long logLsn;
    protected boolean found;
    protected boolean deleted;
    protected int index;
    protected boolean isDuplicate;
    protected Logger logger;
    protected StringBuffer sb;
  }
}
