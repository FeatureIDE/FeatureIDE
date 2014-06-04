package com.sleepycat.je.recovery;
public class Checkpointer {
  private long timeInterval;
  protected void hook545(  long waitTime) throws DatabaseException {
    timeInterval=waitTime;
    original(waitTime);
  }
@MethodObject static class Checkpointer_getWakeupPeriod {
    long execute() throws IllegalArgumentException, DatabaseException {
      wakeupPeriod=PropUtil.microsToMillis(configManager.getLong(EnvironmentParams.CHECKPOINTER_WAKEUP_INTERVAL));
      return original();
    }
    protected void hook540() throws IllegalArgumentException, DatabaseException {
      result+=wakeupPeriod;
      original();
    }
  }
@MethodObject static class Checkpointer_isRunnable {
    protected void hook542() throws DatabaseException {
      if (useTimeInterval != 0) {
        lastUsedLsn=_this.envImpl.getFileManager().getLastUsedLsn();
        if (((System.currentTimeMillis() - _this.lastCheckpointMillis) >= useTimeInterval) && (DbLsn.compareTo(lastUsedLsn,_this.lastCheckpointEnd) != 0)) {
          throw new ReturnBoolean(true);
        }
 else {
          throw new ReturnBoolean(false);
        }
      }
 else {
        original();
      }
    }
    protected void hook543() throws DatabaseException {
      if (config.getMinutes() != 0) {
        useTimeInterval=config.getMinutes() * 60 * 1000;
      }
 else {
        original();
      }
    }
    protected void hook544() throws DatabaseException {
      useTimeInterval=_this.timeInterval;
      original();
    }
  }
}
