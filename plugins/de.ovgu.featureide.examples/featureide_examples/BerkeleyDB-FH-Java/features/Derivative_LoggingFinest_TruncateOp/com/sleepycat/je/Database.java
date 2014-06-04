package com.sleepycat.je;
public class Database {
@MethodObject static class Database_truncate {
    protected void hook39() throws DatabaseException {
      Tracer.trace(Level.FINEST,_this.envHandle.getEnvironmentImpl(),"Database.truncate" + ": txnId=" + ((txn == null) ? "null" : Long.toString(txn.getId())));
      original();
    }
  }
}
