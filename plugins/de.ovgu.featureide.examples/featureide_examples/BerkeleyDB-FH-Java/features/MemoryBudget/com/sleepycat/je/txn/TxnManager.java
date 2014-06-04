package com.sleepycat.je.txn;
public class TxnManager {
  protected void hook828(  Txn txn) throws DatabaseException {
    env.getMemoryBudget().updateMiscMemoryUsage(txn.getAccumulatedDelta() - txn.getInMemorySize());
    original(txn);
  }
  protected void hook829() throws DatabaseException {
    env.getMemoryBudget().updateMiscMemoryUsage(MemoryBudget.HASHMAP_ENTRY_OVERHEAD);
    original();
  }
  protected void hook830() throws DatabaseException {
    env.getMemoryBudget().updateMiscMemoryUsage(0 - MemoryBudget.HASHMAP_ENTRY_OVERHEAD);
    original();
  }
}
