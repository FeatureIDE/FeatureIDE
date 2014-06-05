package com.sleepycat.je.recovery;
public class Checkpointer {
@MethodObject static class Checkpointer_getWakeupPeriod {
    protected void hook519() throws IllegalArgumentException, DatabaseException {
      if ((wakeupPeriod == 0) && (bytePeriod == 0)) {
        throw new IllegalArgumentException(EnvironmentParams.CHECKPOINTER_BYTES_INTERVAL.getName() + " and " + EnvironmentParams.CHECKPOINTER_WAKEUP_INTERVAL.getName()+ " cannot both be 0. ");
      }
      original();
    }
  }
}
