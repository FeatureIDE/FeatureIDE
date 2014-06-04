package com.sleepycat.je.tree;
public final class Tree {
@MethodObject static class Tree_traceInsertDuplicate {
    void execute(){
      logger=env.getLogger();
      if (logger.isLoggable(level)) {
        sb=new StringBuffer();
        sb.append(_this.TRACE_INSERT_DUPLICATE);
        sb.append(" dbin=");
        sb.append(insertingDBin.getNodeId());
        sb.append(" bin=");
        sb.append(binNid);
        sb.append(" ln=");
        sb.append(ln.getNodeId());
        sb.append(" lnLsn=");
        sb.append(DbLsn.getNoFormatString(lnLsn));
        logger.log(level,sb.toString());
      }
      original();
    }
  }
@MethodObject static class Tree_traceInsert {
    void execute(){
      logger=env.getLogger();
      if (logger.isLoggable(level)) {
        sb=new StringBuffer();
        sb.append(_this.TRACE_INSERT);
        sb.append(" bin=");
        sb.append(insertingBin.getNodeId());
        sb.append(" ln=");
        sb.append(ln.getNodeId());
        sb.append(" lnLsn=");
        sb.append(DbLsn.getNoFormatString(lnLsn));
        sb.append(" index=");
        sb.append(index);
        logger.log(level,sb.toString());
      }
      original();
    }
  }
}
