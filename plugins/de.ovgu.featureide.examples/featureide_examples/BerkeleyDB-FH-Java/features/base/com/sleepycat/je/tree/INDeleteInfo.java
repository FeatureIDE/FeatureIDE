package com.sleepycat.je.tree;
import java.nio.ByteBuffer;
import com.sleepycat.je.dbi.DatabaseId;
import com.sleepycat.je.log.LogEntryType;
import com.sleepycat.je.log.LogException;
import com.sleepycat.je.log.LogReadable;
import com.sleepycat.je.log.LogUtils;
import com.sleepycat.je.log.LogWritable;
import com.sleepycat.je.log.LoggableObject;
import de.ovgu.cide.jakutil.*;
/** 
 * INDeleteInfo encapsulates the information logged about the removal of a
 * child from an IN during IN compression.
 */
public class INDeleteInfo implements LoggableObject, LogReadable, LogWritable {
  private long deletedNodeId;
  private byte[] deletedIdKey;
  private DatabaseId dbId;
  /** 
 * Create a new delete info entry.
 */
  public INDeleteInfo(  long deletedNodeId,  byte[] deletedIdKey,  DatabaseId dbId){
    this.deletedNodeId=deletedNodeId;
    this.deletedIdKey=deletedIdKey;
    this.dbId=dbId;
  }
  /** 
 * Used by logging system only.
 */
  public INDeleteInfo(){
    dbId=new DatabaseId();
  }
  public long getDeletedNodeId(){
    return deletedNodeId;
  }
  public byte[] getDeletedIdKey(){
    return deletedIdKey;
  }
  public DatabaseId getDatabaseId(){
    return dbId;
  }
  /** 
 * @see LoggableObject#getLogType
 */
  public LogEntryType getLogType(){
    return LogEntryType.LOG_IN_DELETE_INFO;
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
    return LogUtils.LONG_BYTES + LogUtils.getByteArrayLogSize(deletedIdKey) + dbId.getLogSize();
  }
  /** 
 * @see LogWritable#writeToLog
 */
  public void writeToLog(  ByteBuffer logBuffer){
    LogUtils.writeLong(logBuffer,deletedNodeId);
    LogUtils.writeByteArray(logBuffer,deletedIdKey);
    dbId.writeToLog(logBuffer);
  }
  /** 
 * @see LogReadable#readFromLog
 */
  public void readFromLog(  ByteBuffer itemBuffer,  byte entryTypeVersion) throws LogException {
    deletedNodeId=LogUtils.readLong(itemBuffer);
    deletedIdKey=LogUtils.readByteArray(itemBuffer);
    dbId.readFromLog(itemBuffer,entryTypeVersion);
  }
  /** 
 * @see LogReadable#dumpLog
 */
  public void dumpLog(  StringBuffer sb,  boolean verbose){
    sb.append("<INDeleteEntry node=\"").append(deletedNodeId);
    sb.append("\">");
    sb.append(Key.dumpString(deletedIdKey,0));
    dbId.dumpLog(sb,verbose);
    sb.append("</INDeleteEntry>");
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
}
