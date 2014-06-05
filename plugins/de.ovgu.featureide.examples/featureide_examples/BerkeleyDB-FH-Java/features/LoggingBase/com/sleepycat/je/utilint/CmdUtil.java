package com.sleepycat.je.utilint;
public class CmdUtil {
  protected static void hook855(  EnvironmentConfig config) throws DatabaseException {
    config.setConfigParam(EnvironmentParams.JE_LOGGING_LEVEL.getName(),"SEVERE");
    original(config);
  }
}
