package com.sleepycat.je.dbi;
public class EnvironmentImpl {
  protected void hook317(  DbConfigManager mgr) throws DatabaseException {
    evictor.runOrPause(mgr.getBoolean(EnvironmentParams.ENV_RUN_EVICTOR));
    original(mgr);
  }
}
