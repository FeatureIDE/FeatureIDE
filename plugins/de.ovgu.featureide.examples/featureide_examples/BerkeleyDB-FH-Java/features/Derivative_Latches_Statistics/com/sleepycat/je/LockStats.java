package com.sleepycat.je;
import com.sleepycat.je.latch.LatchStats;
public class LockStats {
  /** 
 * LockTable latch stats.
 */
  private LatchStats lockTableLatchStats;
  /** 
 * Internal use only.
 */
  public void accumulateLockTableLatchStats(  LatchStats latchStats){
    if (lockTableLatchStats == null) {
      lockTableLatchStats=latchStats;
      return;
    }
    lockTableLatchStats.nAcquiresNoWaiters+=latchStats.nAcquiresNoWaiters;
    lockTableLatchStats.nAcquiresSelfOwned+=latchStats.nAcquiresSelfOwned;
    lockTableLatchStats.nAcquiresUpgrade+=latchStats.nAcquiresUpgrade;
    lockTableLatchStats.nAcquiresWithContention+=latchStats.nAcquiresWithContention;
    lockTableLatchStats.nAcquireNoWaitSuccessful+=latchStats.nAcquireNoWaitSuccessful;
    lockTableLatchStats.nAcquireNoWaitUnsuccessful+=latchStats.nAcquireNoWaitUnsuccessful;
    lockTableLatchStats.nAcquireSharedSuccessful+=latchStats.nAcquireSharedSuccessful;
  }
  protected void hook64(  StringBuffer sb){
    sb.append("lockTableLatch:\n").append(lockTableLatchStats);
    original(sb);
  }
}
