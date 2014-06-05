package com.sleepycat.je.dbi;
public class EnvironmentImpl {
  protected void hook315(  StatsConfig config,  EnvironmentStats stats) throws DatabaseException {
    evictor.loadStats(config,stats);
    original(config,stats);
  }
}
