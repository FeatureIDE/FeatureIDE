package com.sleepycat.je.recovery;
public class RecoveryManager {
@MethodObject static class RecoveryManager_trace {
    void execute(){
      logger=database.getDbEnvironment().getLogger();
      useLevel=level;
      if (!success) {
        useLevel=Level.SEVERE;
      }
      if (logger.isLoggable(useLevel)) {
        sb=new StringBuffer();
        sb.append(debugType);
        sb.append(" success=").append(success);
        sb.append(" node=");
        sb.append(node.getNodeId());
        sb.append(" lsn=");
        sb.append(DbLsn.getNoFormatString(logLsn));
        if (parent != null) {
          sb.append(" parent=").append(parent.getNodeId());
        }
        sb.append(" found=");
        sb.append(found);
        sb.append(" replaced=");
        sb.append(replaced);
        sb.append(" inserted=");
        sb.append(inserted);
        if (replacedLsn != DbLsn.NULL_LSN) {
          sb.append(" replacedLsn=");
          sb.append(DbLsn.getNoFormatString(replacedLsn));
        }
        if (abortLsn != DbLsn.NULL_LSN) {
          sb.append(" abortLsn=");
          sb.append(DbLsn.getNoFormatString(abortLsn));
        }
        sb.append(" index=").append(index);
        logger.log(useLevel,sb.toString());
      }
      original();
    }
  }
}
