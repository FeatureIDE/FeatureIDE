package com.sleepycat.je.txn;
import com.sleepycat.je.StatsConfig;
public abstract class LockManager {
  private long nRequests;
  private long nWaits;
  /** 
 * Statistics
 */
  public LockStats lockStat(  StatsConfig config) throws DatabaseException {
    return new LockManager_lockStat(this,config).execute();
  }
  protected void hook774() throws DatabaseException {
    nRequests=0;
    nWaits=0;
    original();
  }
  protected LockAttemptResult attemptLockInternal(  Long nodeId,  Locker locker,  LockType type,  boolean nonBlockingRequest,  int lockTableIndex) throws DatabaseException {
    nRequests++;
    return original(nodeId,locker,type,nonBlockingRequest,lockTableIndex);
  }
  protected void hook775() throws DatabaseException {
    nWaits++;
    original();
  }
  protected void hook776(  LockStats stats,  Map lockTable){
    stats.accumulateNTotalLocks(lockTable.size());
    original(stats,lockTable);
  }
  protected void hook777(  LockStats stats,  Lock lock){
    stats.setNWaiters(stats.getNWaiters() + lock.nWaiters());
    stats.setNOwners(stats.getNOwners() + lock.nOwners());
    original(stats,lock);
  }
  protected void hook778(  LockStats stats,  LockInfo info){
    if (info.getLockType().isWriteLock()) {
      stats.setNWriteLocks(stats.getNWriteLocks() + 1);
    }
 else {
      stats.setNReadLocks(stats.getNReadLocks() + 1);
    }
    original(stats,info);
  }
@MethodObject static class LockManager_lockStat {
    LockManager_lockStat(    LockManager _this,    StatsConfig config){
      this._this=_this;
      this.config=config;
    }
    LockStats execute() throws DatabaseException {
      stats=new LockStats();
      stats.setNRequests(_this.nRequests);
      stats.setNWaits(_this.nWaits);
      if (config.getClear()) {
        _this.nWaits=0;
        _this.nRequests=0;
      }
      this.hook769();
      if (!config.getFast()) {
        _this.dumpLockTable(stats);
      }
      return stats;
    }
    protected LockManager _this;
    protected StatsConfig config;
    protected LockStats stats;
    protected LatchStats latchStats;
    protected void hook769() throws DatabaseException {
    }
  }
}
