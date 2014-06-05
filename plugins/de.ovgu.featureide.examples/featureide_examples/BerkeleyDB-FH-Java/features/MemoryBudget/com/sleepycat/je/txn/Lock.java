package com.sleepycat.je.txn;
public class Lock {
  private static final int REMOVE_LOCKINFO_OVERHEAD=0 - MemoryBudget.LOCKINFO_OVERHEAD;
  protected void hook760(  MemoryBudget mb,  int lockTableIndex){
    mb.updateLockMemoryUsage(MemoryBudget.LOCKINFO_OVERHEAD,lockTableIndex);
    original(mb,lockTableIndex);
  }
  protected void hook761(  MemoryBudget mb,  int lockTableIndex){
    mb.updateLockMemoryUsage(MemoryBudget.LOCKINFO_OVERHEAD,lockTableIndex);
    original(mb,lockTableIndex);
  }
  protected void hook762(  MemoryBudget mb,  int lockTableIndex){
    mb.updateLockMemoryUsage(REMOVE_LOCKINFO_OVERHEAD,lockTableIndex);
    original(mb,lockTableIndex);
  }
  protected void hook763(  MemoryBudget mb,  int lockTableIndex){
    mb.updateLockMemoryUsage(REMOVE_LOCKINFO_OVERHEAD,lockTableIndex);
    original(mb,lockTableIndex);
  }
  protected void hook764(  MemoryBudget mb,  int lockTableIndex){
    mb.updateLockMemoryUsage(MemoryBudget.LOCKINFO_OVERHEAD,lockTableIndex);
    original(mb,lockTableIndex);
  }
  protected void hook765(  MemoryBudget mb,  int lockTableIndex,  boolean removed){
    if (removed) {
      mb.updateLockMemoryUsage(REMOVE_LOCKINFO_OVERHEAD,lockTableIndex);
    }
    original(mb,lockTableIndex,removed);
  }
  protected void hook766(  MemoryBudget mb,  int lockTableIndex,  LockInfo flushedInfo){
    if (flushedInfo != null) {
      mb.updateLockMemoryUsage(REMOVE_LOCKINFO_OVERHEAD,lockTableIndex);
    }
    original(mb,lockTableIndex,flushedInfo);
  }
  protected void hook767(  MemoryBudget mb,  int lockTableIndex){
    mb.updateLockMemoryUsage(REMOVE_LOCKINFO_OVERHEAD,lockTableIndex);
    original(mb,lockTableIndex);
  }
  protected void hook768(  MemoryBudget mb,  int lockTableIndex,  int numRemovedLockInfos) throws DatabaseException {
    mb.updateLockMemoryUsage(0 - (numRemovedLockInfos * MemoryBudget.LOCKINFO_OVERHEAD),lockTableIndex);
    original(mb,lockTableIndex,numRemovedLockInfos);
  }
}
