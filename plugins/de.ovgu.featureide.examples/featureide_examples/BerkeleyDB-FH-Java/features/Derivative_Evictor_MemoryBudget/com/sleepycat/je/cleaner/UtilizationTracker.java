package com.sleepycat.je.cleaner;
public class UtilizationTracker {
@MethodObject static class UtilizationTracker_evictMemory {
    protected void hook196() throws DatabaseException {
      b2&=totalBytes > mb.getTrackerBudget();
      original();
    }
    protected void hook197() throws DatabaseException {
      b1&=mem > largestBytes;
      original();
    }
    protected void hook198() throws DatabaseException {
      mem=tfs.getMemorySize();
      totalBytes+=mem;
      original();
    }
    protected void hook199() throws DatabaseException {
      largestBytes=mem;
      original();
    }
  }
}
