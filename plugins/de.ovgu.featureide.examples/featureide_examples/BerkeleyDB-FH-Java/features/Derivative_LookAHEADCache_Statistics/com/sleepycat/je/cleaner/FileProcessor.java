package com.sleepycat.je.cleaner;
class FileProcessor {
@MethodObject static class FileProcessor_processLN {
    protected void hook117() throws DatabaseException {
      _this.nLNQueueHitsThisRun++;
      _this.nLNsCleanedThisRun++;
      original();
    }
  }
}
