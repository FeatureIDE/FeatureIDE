package com.sleepycat.je.tree;
public final class Tree {
@MethodObject static class Tree_traceMutate {
    void execute(){
      logger=_this.database.getDbEnvironment().getLogger();
      if (logger.isLoggable(level)) {
        sb=new StringBuffer();
        sb.append(_this.TRACE_MUTATE);
        sb.append(" existingLn=");
        sb.append(existingLn.getNodeId());
        sb.append(" newLn=");
        sb.append(newLn.getNodeId());
        sb.append(" newLnLsn=");
        sb.append(DbLsn.getNoFormatString(newLsn));
        sb.append(" dupCountLN=");
        sb.append(dupCountLN.getNodeId());
        sb.append(" dupRootLsn=");
        sb.append(DbLsn.getNoFormatString(dupRootLsn));
        sb.append(" rootdin=");
        sb.append(dupRoot.getNodeId());
        sb.append(" ddinLsn=");
        sb.append(DbLsn.getNoFormatString(ddinLsn));
        sb.append(" dbin=");
        sb.append(dupBin.getNodeId());
        sb.append(" dbinLsn=");
        sb.append(DbLsn.getNoFormatString(dbinLsn));
        sb.append(" bin=");
        sb.append(theBin.getNodeId());
        logger.log(level,sb.toString());
      }
      original();
    }
  }
@MethodObject static class Tree_traceSplitRoot {
    void execute(){
      logger=_this.database.getDbEnvironment().getLogger();
      if (logger.isLoggable(level)) {
        sb=new StringBuffer();
        sb.append(splitType);
        sb.append(" newRoot=").append(newRoot.getNodeId());
        sb.append(" newRootLsn=").append(DbLsn.getNoFormatString(newRootLsn));
        sb.append(" oldRoot=").append(oldRoot.getNodeId());
        sb.append(" oldRootLsn=").append(DbLsn.getNoFormatString(oldRootLsn));
        logger.log(level,sb.toString());
      }
      original();
    }
  }
}
