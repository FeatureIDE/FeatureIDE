package com.sleepycat.je.dbi;
public class CursorImpl {
@MethodObject static class CursorImpl_trace {
    void execute(){
      logger=_this.database.getDbEnvironment().getLogger();
      if (logger.isLoggable(level)) {
        sb=new StringBuffer();
        sb.append(changeType);
        sb.append(" bin=");
        sb.append(theBin.getNodeId());
        sb.append(" ln=");
        sb.append(ln.getNodeId());
        sb.append(" lnIdx=");
        sb.append(lnIndex);
        sb.append(" oldLnLsn=");
        sb.append(DbLsn.getNoFormatString(oldLsn));
        sb.append(" newLnLsn=");
        sb.append(DbLsn.getNoFormatString(newLsn));
        logger.log(level,sb.toString());
      }
      original();
    }
  }
}
