package com.sleepycat.je.dbi;
public class EnvironmentImpl {
  protected void hook314(  StatsConfig config,  EnvironmentStats stats) throws DatabaseException {
    inCompressor.loadStats(config,stats);
    original(config,stats);
  }
}
