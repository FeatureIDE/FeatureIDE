package com.sleepycat.je.txn;
public class Txn {
  private final int READ_LOCK_OVERHEAD=MemoryBudget.HASHSET_ENTRY_OVERHEAD;
  private final int WRITE_LOCK_OVERHEAD=MemoryBudget.HASHMAP_ENTRY_OVERHEAD + MemoryBudget.LONG_OVERHEAD;
  private int accumulatedDelta=0;
  private void updateMemoryUsage(  int delta){
    inMemorySize+=delta;
    accumulatedDelta+=delta;
    if (accumulatedDelta > ACCUMULATED_LIMIT || accumulatedDelta < -ACCUMULATED_LIMIT) {
      envImpl.getMemoryBudget().updateMiscMemoryUsage(accumulatedDelta);
      accumulatedDelta=0;
    }
  }
  int getAccumulatedDelta(){
    return accumulatedDelta;
  }
  protected void hook809() throws DatabaseException {
    updateMemoryUsage(MemoryBudget.TXN_OVERHEAD);
    original();
  }
  protected void hook810(  int delta){
    delta+=READ_LOCK_OVERHEAD;
    updateMemoryUsage(delta);
    original(delta);
  }
  protected int hook811(  int delta){
    delta=MemoryBudget.HASHSET_OVERHEAD;
    return original(delta);
  }
  protected void hook812() throws DatabaseException {
    updateMemoryUsage(0 - READ_LOCK_OVERHEAD);
    original();
  }
  protected void hook813() throws DatabaseException {
    updateMemoryUsage(0 - WRITE_LOCK_OVERHEAD);
    original();
  }
  protected void hook814(){
    updateMemoryUsage(0 - WRITE_LOCK_OVERHEAD);
    original();
  }
@MethodObject static class Txn_addLock {
    protected void hook815() throws DatabaseException {
      delta=0;
      original();
    }
    protected void hook816() throws DatabaseException {
      _this.updateMemoryUsage(delta);
      original();
    }
    protected void hook817() throws DatabaseException {
      delta+=_this.WRITE_LOCK_OVERHEAD;
      original();
    }
    protected void hook818() throws DatabaseException {
      delta+=MemoryBudget.TWOHASHMAPS_OVERHEAD;
      original();
    }
    protected void hook819() throws DatabaseException {
      delta-=_this.READ_LOCK_OVERHEAD;
      original();
    }
  }
}
