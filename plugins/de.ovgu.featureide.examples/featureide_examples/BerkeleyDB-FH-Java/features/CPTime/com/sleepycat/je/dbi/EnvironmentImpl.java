package com.sleepycat.je.dbi;
public class EnvironmentImpl {
@MethodObject static class EnvironmentImpl_createDaemons {
    protected void hook329() throws DatabaseException {
      checkpointerWakeupTime=Checkpointer.getWakeupPeriod(_this.configManager);
      original();
    }
  }
}
