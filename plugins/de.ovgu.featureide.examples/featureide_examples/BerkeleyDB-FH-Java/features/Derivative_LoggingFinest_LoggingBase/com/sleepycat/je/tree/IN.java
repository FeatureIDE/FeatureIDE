package com.sleepycat.je.tree;
public class IN {
@MethodObject static class IN_traceDelete {
    void execute(){
      logger=_this.databaseImpl.getDbEnvironment().getLogger();
      if (logger.isLoggable(level)) {
        sb=new StringBuffer();
        sb.append(_this.TRACE_DELETE);
        sb.append(" in=").append(_this.getNodeId());
        sb.append(" index=");
        sb.append(index);
        logger.log(level,sb.toString());
      }
      original();
    }
  }
}
