package com.sleepycat.je.dbi;
public class MemoryBudget {
@MethodObject static class MemoryBudget_reset {
    protected void hook350() throws DatabaseException {
      newCriticalThreshold=(newMaxMemory * _this.envImpl.getConfigManager().getInt(EnvironmentParams.EVICTOR_CRITICAL_PERCENTAGE)) / 100;
      original();
    }
  }
}
