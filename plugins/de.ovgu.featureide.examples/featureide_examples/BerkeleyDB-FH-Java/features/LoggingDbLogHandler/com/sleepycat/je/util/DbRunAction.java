package com.sleepycat.je.util;
public class DbRunAction {
@MethodObject static class DbRunAction_main {
    protected void hook847() throws Exception {
      if (readOnly) {
        envConfig.setConfigParam(EnvironmentParams.JE_LOGGING_DBLOG.getName(),"false");
        envConfig.setReadOnly(true);
      }
      original();
    }
  }
}
