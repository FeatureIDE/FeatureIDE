package com.sleepycat.je.log;
import com.sleepycat.je.EnvironmentStats;
import com.sleepycat.je.StatsConfig;
abstract public class LogManager {
  private int nRepeatFaultReads;
  private long nTempBufferWrites;
  public void loadStats(  StatsConfig config,  EnvironmentStats stats) throws DatabaseException {
    stats.setNRepeatFaultReads(nRepeatFaultReads);
    stats.setNTempBufferWrites(nTempBufferWrites);
    if (config.getClear()) {
      nRepeatFaultReads=0;
      nTempBufferWrites=0;
    }
    logBufferPool.loadStats(config,stats);
    this.hook497(config,stats);
  }
  protected void hook497(  StatsConfig config,  EnvironmentStats stats) throws DatabaseException {
  }
  protected void hook509() throws IOException, DatabaseException, Exception {
    nTempBufferWrites++;
    original();
  }
@MethodObject static class LogManager_getLogEntryFromLogSource {
    protected void hook508() throws DatabaseException, ClosedChannelException, Exception {
      _this.nRepeatFaultReads++;
      original();
    }
  }
}
