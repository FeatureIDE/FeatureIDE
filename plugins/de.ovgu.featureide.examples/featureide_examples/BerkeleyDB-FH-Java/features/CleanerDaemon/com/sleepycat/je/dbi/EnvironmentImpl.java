package com.sleepycat.je.dbi;
public class EnvironmentImpl {
  /** 
 * public for unit tests.
 */
  public void shutdownCleaner() throws InterruptedException {
    if (cleaner != null) {
      cleaner.shutdown();
    }
    return;
  }
  protected void hook333(  DbConfigManager mgr) throws DatabaseException {
    cleaner.runOrPause(mgr.getBoolean(EnvironmentParams.ENV_RUN_CLEANER) && !mgr.getBoolean(EnvironmentParams.LOG_MEMORY_ONLY));
    original(mgr);
  }
  private void requestShutdownDaemons(){
    original();
    if (cleaner != null) {
      cleaner.requestShutdown();
    }
  }
  /** 
 * Ask all daemon threads to shut down.
 */
  private void shutdownDaemons() throws InterruptedException {
    shutdownCleaner();
    original();
  }
}
