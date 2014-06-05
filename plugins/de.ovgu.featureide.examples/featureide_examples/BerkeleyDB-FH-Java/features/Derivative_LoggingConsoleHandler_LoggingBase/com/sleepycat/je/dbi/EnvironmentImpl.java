package com.sleepycat.je.dbi;
public class EnvironmentImpl {
@MethodObject static class EnvironmentImpl_initLogger {
    Logger execute() throws DatabaseException {
      Logger result=original();
      if (_this.configManager.getBoolean(EnvironmentParams.JE_LOGGING_CONSOLE)) {
        consoleHandler=new ConsoleHandler();
        consoleHandler.setLevel(level);
        logger.addHandler(consoleHandler);
      }
      return result;
    }
  }
}
