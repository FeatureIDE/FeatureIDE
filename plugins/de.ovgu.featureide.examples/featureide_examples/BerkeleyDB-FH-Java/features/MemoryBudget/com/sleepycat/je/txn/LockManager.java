package com.sleepycat.je.txn;
public abstract class LockManager {
  static final long TOTAL_LOCK_OVERHEAD=MemoryBudget.LOCK_OVERHEAD + MemoryBudget.HASHMAP_ENTRY_OVERHEAD + MemoryBudget.LONG_OVERHEAD;
  private static final long REMOVE_TOTAL_LOCK_OVERHEAD=0 - TOTAL_LOCK_OVERHEAD;
  protected void hook779(  DbConfigManager configMgr) throws DatabaseException {
    nLockTables=configMgr.getInt(EnvironmentParams.N_LOCK_TABLES);
    original(configMgr);
  }
  protected void hook780(  int lockTableIndex) throws DatabaseException {
    memoryBudget.updateLockMemoryUsage(TOTAL_LOCK_OVERHEAD,lockTableIndex);
    original(lockTableIndex);
  }
  protected void hook781(  int lockTableIndex) throws DatabaseException {
    memoryBudget.updateLockMemoryUsage(REMOVE_TOTAL_LOCK_OVERHEAD,lockTableIndex);
    original(lockTableIndex);
  }
}
