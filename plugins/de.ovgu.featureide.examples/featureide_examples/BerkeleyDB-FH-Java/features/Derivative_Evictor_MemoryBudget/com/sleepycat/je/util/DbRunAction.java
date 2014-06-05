package com.sleepycat.je.util;
public class DbRunAction {
@MethodObject static class DbRunAction_doEvict {
    protected void hook836() throws DatabaseException {
      c.setCacheSize(cacheUsage / 2);
      original();
    }
    protected void hook837() throws DatabaseException {
      cacheUsage=envImpl.getMemoryBudget().getCacheMemoryUsage();
      original();
    }
  }
}
