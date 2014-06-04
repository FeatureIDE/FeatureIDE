package com.sleepycat.je.recovery;
public class RecoveryManager {
@MethodObject static class RecoveryManager_traceRootDeletion {
    void execute(){
      logger=database.getDbEnvironment().getLogger();
      if (logger.isLoggable(level)) {
        sb=new StringBuffer();
        sb.append(TRACE_ROOT_DELETE);
        sb.append(" Dbid=").append(database.getId());
        logger.log(level,sb.toString());
      }
      original();
    }
  }
}
