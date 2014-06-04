package com.sleepycat.je.utilint;
public class CmdUtil {
  protected static void hook854(  EnvironmentConfig config) throws DatabaseException {
    config.setConfigParam(EnvironmentParams.JE_LOGGING_CONSOLE.getName(),"true");
    original(config);
  }
}
