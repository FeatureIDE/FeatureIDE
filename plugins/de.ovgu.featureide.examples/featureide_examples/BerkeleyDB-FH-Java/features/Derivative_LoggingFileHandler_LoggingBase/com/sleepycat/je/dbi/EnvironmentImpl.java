package com.sleepycat.je.dbi;
public class EnvironmentImpl {
  /** 
 * Flip the log to a new file, forcing an fsync. Return the LSN of the trace
 * record in the new file.
 */
  public long forceLogFileFlip() throws DatabaseException {
    Tracer newRec=new Tracer("File Flip");
    return logManager.logForceFlip(newRec);
  }
@MethodObject static class EnvironmentImpl_initLogger {
    Logger execute() throws DatabaseException {
      Logger result=original();
      fileHandler=null;
      try {
        if (_this.configManager.getBoolean(EnvironmentParams.JE_LOGGING_FILE)) {
          limit=_this.configManager.getInt(EnvironmentParams.JE_LOGGING_FILE_LIMIT);
          count=_this.configManager.getInt(EnvironmentParams.JE_LOGGING_FILE_COUNT);
          logFilePattern=envHome + "/" + Tracer.INFO_FILES;
          fileHandler=new FileHandler(logFilePattern,limit,count,true);
          fileHandler.setFormatter(new SimpleFormatter());
          fileHandler.setLevel(level);
          logger.addHandler(fileHandler);
        }
      }
 catch (      IOException e) {
        throw new DatabaseException(e.getMessage());
      }
      return result;
    }
  }
}
