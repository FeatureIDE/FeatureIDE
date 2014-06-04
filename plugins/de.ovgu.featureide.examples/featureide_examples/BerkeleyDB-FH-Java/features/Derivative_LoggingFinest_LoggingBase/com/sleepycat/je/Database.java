package com.sleepycat.je;
public class Database {
@MethodObject static class Database_trace2 {
    void execute() throws DatabaseException {
      if (_this.logger.isLoggable(level)) {
        sb=new StringBuffer();
        sb.append(methodName);
        sb.append(" name=" + _this.getDebugName());
        if (txn != null) {
          sb.append(" txnId=").append(txn.getId());
        }
        if (config != null) {
          sb.append(" config=").append(config);
        }
        _this.logger.log(level,sb.toString());
      }
      original();
    }
  }
@MethodObject static class Database_trace {
    void execute() throws DatabaseException {
      if (_this.logger.isLoggable(level)) {
        sb=new StringBuffer();
        sb.append(methodName);
        if (txn != null) {
          sb.append(" txnId=").append(txn.getId());
        }
        sb.append(" key=").append(key.dumpData());
        if (data != null) {
          sb.append(" data=").append(data.dumpData());
        }
        if (lockMode != null) {
          sb.append(" lockMode=").append(lockMode);
        }
        _this.logger.log(level,sb.toString());
      }
      original();
    }
  }
}
