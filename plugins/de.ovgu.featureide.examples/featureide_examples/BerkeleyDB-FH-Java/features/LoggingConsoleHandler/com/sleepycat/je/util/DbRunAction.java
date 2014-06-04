package com.sleepycat.je.util;
public class DbRunAction {
@MethodObject static class DbRunAction_main {
    protected void hook848() throws Exception {
      envConfig.setConfigParam(EnvironmentParams.JE_LOGGING_CONSOLE.getName(),"true");
      original();
    }
  }
}
