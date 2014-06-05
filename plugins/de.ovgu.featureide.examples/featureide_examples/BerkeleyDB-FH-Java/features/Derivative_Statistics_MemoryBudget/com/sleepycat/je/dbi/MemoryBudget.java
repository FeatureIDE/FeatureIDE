package com.sleepycat.je.dbi;
public class MemoryBudget {
  void loadStats(  StatsConfig config,  EnvironmentStats stats){
    stats.setCacheDataBytes(getCacheMemoryUsage());
  }
}
