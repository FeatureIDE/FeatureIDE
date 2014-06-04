package com.sleepycat.je;
public class SecondaryDatabase {
@MethodObject static class SecondaryDatabase_trace {
    void execute() throws DatabaseException {
      logger=envHandle.getEnvironmentImpl().getLogger();
      if (logger.isLoggable(level)) {
        sb=new StringBuffer();
        sb.append(methodName);
        sb.append(" name=").append(_this.getDebugName());
        sb.append(" primary=").append(_this.primaryDb.getDebugName());
        logger.log(level,sb.toString());
      }
      original();
    }
  }
}
