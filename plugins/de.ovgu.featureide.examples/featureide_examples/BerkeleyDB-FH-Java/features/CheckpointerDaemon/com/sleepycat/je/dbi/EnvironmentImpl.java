package com.sleepycat.je.dbi;
public class EnvironmentImpl {
  protected void hook326(  DbConfigManager mgr) throws DatabaseException {
    checkpointer.runOrPause(mgr.getBoolean(EnvironmentParams.ENV_RUN_CHECKPOINTER));
    original(mgr);
  }
  protected void hook327(){
    if (checkpointer != null) {
      checkpointer.requestShutdown();
    }
    original();
  }
  protected void hook328() throws InterruptedException {
    checkpointer.shutdown();
    checkpointer.clearEnv();
    original();
  }
}
