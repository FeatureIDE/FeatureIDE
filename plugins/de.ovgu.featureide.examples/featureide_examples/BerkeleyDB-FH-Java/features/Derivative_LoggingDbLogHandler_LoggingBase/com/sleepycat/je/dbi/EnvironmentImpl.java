package com.sleepycat.je.dbi;
public class EnvironmentImpl {
  /** 
 * Add the database log as one of the debug logging destinations when the
 * logging system is sufficiently initialized.
 */
  public void enableDebugLoggingToDbLog() throws DatabaseException {
    if (configManager.getBoolean(EnvironmentParams.JE_LOGGING_DBLOG)) {
      Handler dbLogHandler=new TraceLogHandler(this);
      Level level=Level.parse(configManager.get(EnvironmentParams.JE_LOGGING_LEVEL));
      dbLogHandler.setLevel(level);
      envLogger.addHandler(dbLogHandler);
    }
  }
}
