package com.sleepycat.je;
public class Cursor {
@MethodObject static class Cursor_trace {
    void execute(){
      if (_this.logger.isLoggable(level)) {
        sb=new StringBuffer();
        sb.append(methodName);
        _this.traceCursorImpl(sb);
        if (key != null) {
          sb.append(" key=").append(key.dumpData());
        }
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
@MethodObject static class Cursor_trace2 {
    void execute(){
      if (_this.logger.isLoggable(level)) {
        sb=new StringBuffer();
        sb.append(methodName);
        _this.traceCursorImpl(sb);
        if (lockMode != null) {
          sb.append(" lockMode=").append(lockMode);
        }
        _this.logger.log(level,sb.toString());
      }
      original();
    }
  }
}
