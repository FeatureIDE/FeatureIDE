package com.sleepycat.je.dbi;
public class EnvironmentImpl {
  protected void hook316(  StatsConfig config,  EnvironmentStats stats) throws DatabaseException {
    memoryBudget.loadStats(config,stats);
    original(config,stats);
  }
}
