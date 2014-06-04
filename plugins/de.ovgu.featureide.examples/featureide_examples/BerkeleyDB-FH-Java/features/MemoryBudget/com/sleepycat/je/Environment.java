package com.sleepycat.je;
public class Environment {
  /** 
 * Returns the current memory usage in bytes for all btrees in the
 * environmentImpl.
 */
  long getMemoryUsage() throws DatabaseException {
    checkHandleIsValid();
    checkEnv();
    return environmentImpl.getMemoryBudget().getCacheMemoryUsage();
  }
}
