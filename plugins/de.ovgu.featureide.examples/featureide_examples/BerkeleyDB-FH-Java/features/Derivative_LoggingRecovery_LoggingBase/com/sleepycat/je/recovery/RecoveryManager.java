package com.sleepycat.je.recovery;
public class RecoveryManager {
  protected static void hook555(  Level traceLevel,  DatabaseImpl db,  TreeLocation location,  LN lnFromLog,  long logLsn,  long abortLsn,  boolean found,  boolean replaced,  boolean success) throws DatabaseException {
    trace(traceLevel,db,TRACE_LN_UNDO,success,lnFromLog,logLsn,location.bin,found,replaced,false,location.childLsn,abortLsn,location.index);
    original(traceLevel,db,location,lnFromLog,logLsn,abortLsn,found,replaced,success);
  }
@MethodObject static class RecoveryManager_traceINDeleteReplay {
    void execute(){
      logger=_this.env.getLogger();
      if (logger.isLoggable(_this.detailedTraceLevel)) {
        sb=new StringBuffer();
        sb.append((isDuplicate) ? _this.TRACE_IN_DUPDEL_REPLAY : _this.TRACE_IN_DEL_REPLAY);
        sb.append(" node=").append(nodeId);
        sb.append(" lsn=").append(DbLsn.getNoFormatString(logLsn));
        sb.append(" found=").append(found);
        sb.append(" deleted=").append(deleted);
        sb.append(" index=").append(index);
        logger.log(_this.detailedTraceLevel,sb.toString());
      }
      original();
    }
  }
}
