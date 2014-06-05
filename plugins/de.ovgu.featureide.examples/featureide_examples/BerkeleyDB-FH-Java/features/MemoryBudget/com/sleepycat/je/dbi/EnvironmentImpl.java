package com.sleepycat.je.dbi;
public class EnvironmentImpl {
  protected void hook335() throws DatabaseException {
    memoryBudget.initCacheMemoryUsage();
    original();
  }
}
