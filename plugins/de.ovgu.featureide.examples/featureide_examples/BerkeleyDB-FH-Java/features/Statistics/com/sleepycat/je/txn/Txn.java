package com.sleepycat.je.txn;
public class Txn {
  /** 
 * stats
 */
  public LockStats collectStats(  LockStats stats) throws DatabaseException {
synchronized (this) {
      int nReadLocks=(readLocks == null) ? 0 : readLocks.size();
      stats.setNReadLocks(stats.getNReadLocks() + nReadLocks);
      int nWriteLocks=(writeInfo == null) ? 0 : writeInfo.size();
      stats.setNWriteLocks(stats.getNWriteLocks() + nWriteLocks);
    }
    return stats;
  }
}
