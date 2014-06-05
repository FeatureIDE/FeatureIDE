package com.sleepycat.je.tree;
public class IN {
@MethodObject static class IN_traceSplit {
    void execute(){
      logger=_this.databaseImpl.getDbEnvironment().getLogger();
      if (logger.isLoggable(level)) {
        sb=new StringBuffer();
        sb.append(_this.TRACE_SPLIT);
        sb.append(" parent=");
        sb.append(parent.getNodeId());
        sb.append(" child=");
        sb.append(_this.getNodeId());
        sb.append(" newSibling=");
        sb.append(newSibling.getNodeId());
        sb.append(" parentLsn = ");
        sb.append(DbLsn.getNoFormatString(parentLsn));
        sb.append(" childLsn = ");
        sb.append(DbLsn.getNoFormatString(myNewLsn));
        sb.append(" newSiblingLsn = ");
        sb.append(DbLsn.getNoFormatString(newSiblingLsn));
        sb.append(" splitIdx=");
        sb.append(splitIndex);
        sb.append(" idKeyIdx=");
        sb.append(idKeyIndex);
        sb.append(" childIdx=");
        sb.append(childIndex);
        logger.log(level,sb.toString());
      }
      original();
    }
  }
}
