package com.sleepycat.je.txn;
import com.sleepycat.je.latch.LatchStats;
public abstract class LockManager {
@MethodObject static class LockManager_lockStat {
    protected void hook769() throws DatabaseException {
      for (int i=0; i < _this.nLockTables; i++) {
        latchStats=(LatchStats)_this.lockTableLatches[i].getLatchStats();
        stats.accumulateLockTableLatchStats(latchStats);
      }
      original();
    }
  }
}
