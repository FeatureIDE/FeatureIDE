package com.sleepycat.je.txn;
public class Txn {
@MethodObject static class Txn_traceCommit {
    void execute(){
      original();
      if (logger.isLoggable(Level.FINE)) {
        sb=new StringBuffer();
        sb.append(" Commit:id = ").append(id);
        sb.append(" numWriteLocks=").append(numWriteLocks);
        sb.append(" numReadLocks = ").append(numReadLocks);
        Tracer.trace(Level.FINE,envImpl,sb.toString());
      }
    }
  }
}
