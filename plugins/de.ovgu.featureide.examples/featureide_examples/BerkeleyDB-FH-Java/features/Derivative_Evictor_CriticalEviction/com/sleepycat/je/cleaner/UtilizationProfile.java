package com.sleepycat.je.cleaner;
public class UtilizationProfile {
  protected void hook173() throws DatabaseException {
    env.getEvictor().doCriticalEviction();
    original();
  }
  protected void hook174() throws DatabaseException {
    env.getEvictor().doCriticalEviction();
    original();
  }
  protected void hook175() throws DatabaseException {
    env.getEvictor().doCriticalEviction();
    original();
  }
@MethodObject static class UtilizationProfile_populateCache {
    protected void hook176() throws DatabaseException {
      _this.env.getEvictor().doCriticalEviction();
      original();
    }
  }
}
