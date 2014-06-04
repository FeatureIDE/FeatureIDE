package com.sleepycat.je.recovery;
public class Checkpointer {
  private long logSizeBytesInterval;
  protected void hook539(  EnvironmentImpl envImpl) throws DatabaseException {
    logSizeBytesInterval=envImpl.getConfigManager().getLong(EnvironmentParams.CHECKPOINTER_BYTES_INTERVAL);
    original(envImpl);
  }
@MethodObject static class Checkpointer_getWakeupPeriod {
    protected void hook540() throws IllegalArgumentException, DatabaseException {
      if (bytePeriod == 0) {
        original();
      }
    }
    protected void hook541() throws IllegalArgumentException, DatabaseException {
      bytePeriod=configManager.getLong(EnvironmentParams.CHECKPOINTER_BYTES_INTERVAL);
      original();
    }
  }
@MethodObject static class Checkpointer_isRunnable {
    protected void hook542() throws DatabaseException {
      if (useBytesInterval != 0) {
        nextLsn=_this.envImpl.getFileManager().getNextLsn();
        if (DbLsn.getNoCleaningDistance(nextLsn,_this.lastCheckpointEnd,_this.logFileMax) >= useBytesInterval) {
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
      if (config.getKBytes() != 0) {
        useBytesInterval=config.getKBytes() << 10;
      }
 else {
        original();
      }
    }
    protected void hook544() throws DatabaseException {
      if (_this.logSizeBytesInterval != 0) {
        useBytesInterval=_this.logSizeBytesInterval;
      }
 else {
        original();
      }
    }
  }
}
