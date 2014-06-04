package com.sleepycat.je.cleaner;
public class Cleaner {
@MethodObject static class Cleaner_processPending {
    protected void hook86() throws DatabaseException {
      _this.env.getEvictor().doCriticalEviction();
      original();
    }
  }
}
