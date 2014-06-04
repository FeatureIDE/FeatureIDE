package com.sleepycat.je.recovery;
import java.nio.ByteBuffer;
import java.sql.Timestamp;
import java.util.Calendar;
import com.sleepycat.je.log.LogEntryType;
import com.sleepycat.je.log.LogException;
import com.sleepycat.je.log.LogReadable;
import com.sleepycat.je.log.LogUtils;
import com.sleepycat.je.log.LoggableObject;
import com.sleepycat.je.utilint.DbLsn;
import de.ovgu.cide.jakutil.*;
/** 
 * CheckpointEnd encapsulates the information needed by a checkpoint end 
 * log entry.
 */
public class CheckpointEnd implements LoggableObject, LogReadable {
  private String invoker;
  private Timestamp endTime;
  private long checkpointStartLsn;
  private boolean rootLsnExists;
  private long rootLsn;
  private long firstActiveLsn;
  private long lastNodeId;
  private int lastDbId;
  private long lastTxnId;
  private long id;
  public CheckpointEnd(  String invoker,  long checkpointStartLsn,  long rootLsn,  long firstActiveLsn,  long lastNodeId,  int lastDbId,  long lastTxnId,  long id){
    if (invoker == null) {
      this.invoker="";
    }
 else {
      this.invoker=invoker;
    }
    Calendar cal=Calendar.getInstance();
    this.endTime=new Timestamp(cal.getTime().getTime());
    this.checkpointStartLsn=checkpointStartLsn;
    this.rootLsn=rootLsn;
    if (rootLsn == DbLsn.NULL_LSN) {
      rootLsnExists=false;
    }
 else {
      rootLsnExists=true;
    }
    if (firstActiveLsn == DbLsn.NULL_LSN) {
      this.firstActiveLsn=checkpointStartLsn;
    }
 else {
      this.firstActiveLsn=firstActiveLsn;
    }
    this.lastNodeId=lastNodeId;
    this.lastDbId=lastDbId;
    this.lastTxnId=lastTxnId;
    this.id=id;
  }
  public CheckpointEnd(){
    checkpointStartLsn=DbLsn.NULL_LSN;
    rootLsn=DbLsn.NULL_LSN;
    firstActiveLsn=DbLsn.NULL_LSN;
  }
  /** 
 * @see LoggableObject#getLogType
 */
  public LogEntryType getLogType(){
    return LogEntryType.LOG_CKPT_END;
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
 * @see LoggableObject#getLogSize
 */
  public int getLogSize(){
    int size=LogUtils.getStringLogSize(invoker) + LogUtils.getTimestampLogSize() + LogUtils.getLongLogSize()+ LogUtils.getBooleanLogSize()+ LogUtils.getLongLogSize()+ LogUtils.getLongLogSize()+ LogUtils.getIntLogSize()+ LogUtils.getLongLogSize()+ LogUtils.getLongLogSize();
    if (rootLsnExists) {
      size+=LogUtils.getLongLogSize();
    }
    return size;
  }
  /** 
 * @see LoggableObject#writeToLog
 */
  public void writeToLog(  ByteBuffer logBuffer){
    LogUtils.writeString(logBuffer,invoker);
    LogUtils.writeTimestamp(logBuffer,endTime);
    LogUtils.writeLong(logBuffer,checkpointStartLsn);
    LogUtils.writeBoolean(logBuffer,rootLsnExists);
    if (rootLsnExists) {
      LogUtils.writeLong(logBuffer,rootLsn);
    }
    LogUtils.writeLong(logBuffer,firstActiveLsn);
    LogUtils.writeLong(logBuffer,lastNodeId);
    LogUtils.writeInt(logBuffer,lastDbId);
    LogUtils.writeLong(logBuffer,lastTxnId);
    LogUtils.writeLong(logBuffer,id);
  }
  /** 
 * @see LogReadable#readFromLog
 */
  public void readFromLog(  ByteBuffer logBuffer,  byte entryTypeVersion) throws LogException {
    invoker=LogUtils.readString(logBuffer);
    endTime=LogUtils.readTimestamp(logBuffer);
    checkpointStartLsn=LogUtils.readLong(logBuffer);
    rootLsnExists=LogUtils.readBoolean(logBuffer);
    if (rootLsnExists) {
      rootLsn=LogUtils.readLong(logBuffer);
    }
    firstActiveLsn=LogUtils.readLong(logBuffer);
    lastNodeId=LogUtils.readLong(logBuffer);
    lastDbId=LogUtils.readInt(logBuffer);
    lastTxnId=LogUtils.readLong(logBuffer);
    id=LogUtils.readLong(logBuffer);
  }
  /** 
 * @see LogReadable#dumpLog
 */
  public void dumpLog(  StringBuffer sb,  boolean verbose){
    sb.append("<CkptEnd invoker=\"").append(invoker);
    sb.append("\" time=\"").append(endTime);
    sb.append("\" lastNodeId=\"").append(lastNodeId);
    sb.append("\" lastDbId=\"").append(lastDbId);
    sb.append("\" lastTxnId=\"").append(lastTxnId);
    sb.append("\" id=\"").append(id);
    sb.append("\" rootExists=\"").append(rootLsnExists);
    sb.append("\">");
    sb.append("<ckptStart>");
    sb.append(DbLsn.toString(checkpointStartLsn));
    sb.append("</ckptStart>");
    if (rootLsnExists) {
      sb.append("<root>");
      sb.append(DbLsn.toString(rootLsn));
      sb.append("</root>");
    }
    sb.append("<firstActive>");
    sb.append(DbLsn.toString(firstActiveLsn));
    sb.append("</firstActive>");
    sb.append("</CkptEnd>");
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
    StringBuffer sb=new StringBuffer();
    sb.append("time=").append(endTime);
    sb.append(" lastNodeId=").append(lastNodeId);
    sb.append(" lastDbId=").append(lastDbId);
    sb.append(" lastTxnId=").append(lastTxnId);
    sb.append(" id=").append(id);
    sb.append(" rootExists=").append(rootLsnExists);
    sb.append(" ckptStartLsn=").append(DbLsn.getNoFormatString(checkpointStartLsn));
    if (rootLsnExists) {
      sb.append(" root=").append(DbLsn.getNoFormatString(rootLsn));
    }
    sb.append(" firstActive=").append(DbLsn.getNoFormatString(firstActiveLsn));
    return sb.toString();
  }
  long getCheckpointStartLsn(){
    return checkpointStartLsn;
  }
  long getRootLsn(){
    return rootLsn;
  }
  long getFirstActiveLsn(){
    return firstActiveLsn;
  }
  long getLastNodeId(){
    return lastNodeId;
  }
  int getLastDbId(){
    return lastDbId;
  }
  long getLastTxnId(){
    return lastTxnId;
  }
  long getId(){
    return id;
  }
}
