package com.sleepycat.je.txn;
public class BasicLocker {
  /** 
 * stats
 */
  public LockStats collectStats(  LockStats stats) throws DatabaseException {
    if (ownedLock != null) {
      if (ownedLock.isOwnedWriteLock(this)) {
        stats.setNWriteLocks(stats.getNWriteLocks() + 1);
      }
 else {
        stats.setNReadLocks(stats.getNReadLocks() + 1);
      }
    }
    if (ownedLockSet != null) {
      Iterator iter=ownedLockSet.iterator();
      while (iter.hasNext()) {
        Lock l=(Lock)iter.next();
        if (l.isOwnedWriteLock(this)) {
          stats.setNWriteLocks(stats.getNWriteLocks() + 1);
        }
 else {
          stats.setNReadLocks(stats.getNReadLocks() + 1);
        }
      }
    }
    return stats;
  }
}
