package com.sleepycat.je;
public class Environment {
  /** 
 * Javadoc for this public method is generated via the doc templates in the
 * doc_src directory.
 */
  public void evictMemory() throws DatabaseException {
    checkHandleIsValid();
    checkEnv();
    environmentImpl.invokeEvictor();
  }
}
