package com.sleepycat.je.utilint;
public class CmdUtil {
  protected static void hook853(  EnvironmentConfig config) throws DatabaseException {
    config.setConfigParam(EnvironmentParams.JE_LOGGING_DBLOG.getName(),"false");
    original(config);
  }
}
