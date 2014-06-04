package com.sleepycat.je.cleaner;
public class Cleaner {
@MethodObject static class Cleaner_trace {
    void execute(){
      logger=_this.env.getLogger();
      if (logger.isLoggable(level)) {
        sb=new StringBuffer();
        sb.append(action);
        if (node != null) {
          sb.append(" node=");
          sb.append(node.getNodeId());
        }
        sb.append(" logLsn=");
        sb.append(DbLsn.getNoFormatString(logLsn));
        sb.append(" complete=").append(completed);
        sb.append(" obsolete=").append(obsolete);
        sb.append(" dirtiedOrMigrated=").append(dirtiedMigrated);
        logger.log(level,sb.toString());
      }
      original();
    }
  }
}
