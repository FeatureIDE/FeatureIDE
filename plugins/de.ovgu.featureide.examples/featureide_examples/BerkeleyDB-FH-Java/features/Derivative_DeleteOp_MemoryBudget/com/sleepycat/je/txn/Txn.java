package com.sleepycat.je.txn;
public class Txn {
@MethodObject static class Txn_markDeleteAtTxnEnd {
    protected void hook796() throws DatabaseException {
      delta+=MemoryBudget.HASHSET_ENTRY_OVERHEAD + MemoryBudget.OBJECT_OVERHEAD;
      _this.updateMemoryUsage(delta);
      original();
    }
    protected void hook797() throws DatabaseException {
      delta=0;
      original();
    }
    protected void hook798() throws DatabaseException {
      delta+=MemoryBudget.HASHSET_OVERHEAD;
      original();
    }
  }
}
