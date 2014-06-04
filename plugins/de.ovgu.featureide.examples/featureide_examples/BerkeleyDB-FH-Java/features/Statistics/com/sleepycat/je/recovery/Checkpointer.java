package com.sleepycat.je.recovery;
import com.sleepycat.je.EnvironmentStats;
import com.sleepycat.je.StatsConfig;
public class Checkpointer {
  private int nCheckpoints;
  private long lastCheckpointStart;
  private int nFullINFlush;
  private int nFullBINFlush;
  private int nDeltaINFlush;
  private int nFullINFlushThisRun;
  private int nDeltaINFlushThisRun;
  /** 
 * Load stats.
 */
  public void loadStats(  StatsConfig config,  EnvironmentStats stat) throws DatabaseException {
    stat.setNCheckpoints(nCheckpoints);
    stat.setLastCheckpointStart(lastCheckpointStart);
    stat.setLastCheckpointEnd(lastCheckpointEnd);
    stat.setLastCheckpointId(checkpointId);
    stat.setNFullINFlush(nFullINFlush);
    stat.setNFullBINFlush(nFullBINFlush);
    stat.setNDeltaINFlush(nDeltaINFlush);
    if (config.getClear()) {
      nCheckpoints=0;
      nFullINFlush=0;
      nFullBINFlush=0;
      nDeltaINFlush=0;
    }
  }
  /** 
 * Reset per-run counters.
 */
  private void resetPerRunCounters(){
    nFullINFlushThisRun=0;
    nDeltaINFlushThisRun=0;
  }
  protected void hook531() throws DatabaseException {
    nCheckpoints=0;
    original();
  }
  protected void hook532() throws DatabaseException {
    nFullINFlushThisRun++;
    nFullINFlush++;
    original();
  }
  protected void hook533(  IN target) throws DatabaseException {
    nFullINFlushThisRun++;
    nFullINFlush++;
    if (target instanceof BIN) {
      nFullBINFlush++;
    }
    original(target);
  }
  protected void hook537() throws DatabaseException {
    nDeltaINFlushThisRun++;
    nDeltaINFlush++;
    original();
  }
@MethodObject static class Checkpointer_doCheckpoint {
    protected void hook534() throws DatabaseException {
      _this.nCheckpoints++;
      original();
    }
    protected void hook535() throws DatabaseException {
      _this.resetPerRunCounters();
      original();
    }
    protected void hook536() throws DatabaseException {
      _this.lastCheckpointStart=checkpointStart;
      original();
    }
  }
}
