package com.sleepycat.je.log;
abstract public class LogManager {
  protected void hook497(  StatsConfig config,  EnvironmentStats stats) throws DatabaseException {
    fileManager.loadStats(config,stats);
    original(config,stats);
  }
}
