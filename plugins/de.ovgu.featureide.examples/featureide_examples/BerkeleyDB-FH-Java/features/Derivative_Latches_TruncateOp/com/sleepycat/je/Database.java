package com.sleepycat.je;
public class Database {
@MethodObject static class Database_truncate {
    protected void hook40() throws DatabaseException {
      triggerLock=false;
      original();
    }
    protected void hook41() throws DatabaseException {
      triggerLock=true;
      original();
    }
    protected void hook42() throws DatabaseException {
      if (triggerLock) {
        _this.releaseTriggerListReadLock();
      }
      original();
    }
  }
}
