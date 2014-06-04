package com.sleepycat.je.utilint;
public class Tracer implements LoggableObject, LogReadable {
  /** 
 * @see LoggableObject#getLogType
 */
  public LogEntryType getLogType(){
    return LogEntryType.LOG_TRACE;
  }
  /** 
 * @see LoggableObject#marshallOutsideWriteLatchCan be marshalled outside the log write latch.
 */
  public boolean marshallOutsideWriteLatch(){
    return true;
  }
  /** 
 * @see LoggableObject#countAsObsoleteWhenLogged
 */
  public boolean countAsObsoleteWhenLogged(){
    return false;
  }
  /** 
 * @see LoggableObject#postLogWork
 */
  public void postLogWork(  long justLoggedLsn){
  }
  /** 
 * @see LoggableObject#getLogSize()
 */
  public int getLogSize(){
    return (LogUtils.getTimestampLogSize() + LogUtils.getStringLogSize(msg));
  }
  /** 
 * @see LoggableObject#writeToLog
 */
  public void writeToLog(  ByteBuffer logBuffer){
    LogUtils.writeTimestamp(logBuffer,time);
    LogUtils.writeString(logBuffer,msg);
  }
  /** 
 * @see LogReadable#readFromLog
 */
  public void readFromLog(  ByteBuffer itemBuffer,  byte entryTypeVersion){
    time=LogUtils.readTimestamp(itemBuffer);
    msg=LogUtils.readString(itemBuffer);
  }
  /** 
 * @see LogReadable#dumpLog
 */
  public void dumpLog(  StringBuffer sb,  boolean verbose){
    sb.append("<Dbg time=\"");
    sb.append(time);
    sb.append("\">");
    sb.append("<msg val=\"");
    sb.append(msg);
    sb.append("\"/>");
    sb.append("</Dbg>");
  }
  /** 
 * @see LogReadable#logEntryIsTransactional
 */
  public boolean logEntryIsTransactional(){
    return false;
  }
  /** 
 * @see LogReadable#getTransactionId
 */
  public long getTransactionId(){
    return 0;
  }
  public String toString(){
    return (time + "/" + msg);
  }
  /** 
 * Just in case it's ever used as a hash key.
 */
  public int hashCode(){
    return toString().hashCode();
  }
  /** 
 * Override Object.equals
 */
  public boolean equals(  Object obj){
    if (this == obj) {
      return true;
    }
    if (!(obj instanceof Tracer)) {
      return false;
    }
    return (toString().equals(obj.toString()));
  }
}
