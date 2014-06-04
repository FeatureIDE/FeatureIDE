package com.sleepycat.je.cleaner;
class FileProcessor {
@MethodObject static class FileProcessor_processFile {
    protected void hook119() throws DatabaseException, IOException {
      if (Cleaner.DO_CRITICAL_EVICTION) {
        _this.env.getEvictor().doCriticalEviction();
      }
      original();
    }
    protected void hook120() throws DatabaseException, IOException {
      if (Cleaner.DO_CRITICAL_EVICTION) {
        _this.env.getEvictor().doCriticalEviction();
      }
      original();
    }
  }
}
