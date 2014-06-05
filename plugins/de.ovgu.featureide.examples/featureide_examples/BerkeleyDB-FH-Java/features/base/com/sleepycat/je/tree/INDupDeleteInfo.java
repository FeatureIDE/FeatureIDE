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
 * INDupDeleteInfo encapsulates the information logged about the removal of a
 * child from a duplicate IN during IN compression.
 */
public class INDupDeleteInfo implements LoggableObject, LogReadable, LogWritable {
  private long deletedNodeId;
  private byte[] deletedMainKey;
  private byte[] deletedDupKey;
  private DatabaseId dbId;
  /** 
 * Create a new delete info entry.
 */
  public INDupDeleteInfo(  long deletedNodeId,  byte[] deletedMainKey,  byte[] deletedDupKey,  DatabaseId dbId){
    this.deletedNodeId=deletedNodeId;
    this.deletedMainKey=deletedMainKey;
    this.deletedDupKey=deletedDupKey;
    this.dbId=dbId;
  }
  /** 
 * Used by logging system only.
 */
  public INDupDeleteInfo(){
    dbId=new DatabaseId();
  }
  public long getDeletedNodeId(){
    return deletedNodeId;
  }
  public byte[] getDeletedMainKey(){
    return deletedMainKey;
  }
  public byte[] getDeletedDupKey(){
    return deletedDupKey;
  }
  public DatabaseId getDatabaseId(){
    return dbId;
  }
  /** 
 * @see LoggableObject#getLogType
 */
  public LogEntryType getLogType(){
    return LogEntryType.LOG_IN_DUPDELETE_INFO;
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
    return LogUtils.LONG_BYTES + LogUtils.getByteArrayLogSize(deletedMainKey) + LogUtils.getByteArrayLogSize(deletedDupKey)+ dbId.getLogSize();
  }
  /** 
 * @see LogWritable#writeToLog
 */
  public void writeToLog(  ByteBuffer logBuffer){
    LogUtils.writeLong(logBuffer,deletedNodeId);
    LogUtils.writeByteArray(logBuffer,deletedMainKey);
    LogUtils.writeByteArray(logBuffer,deletedDupKey);
    dbId.writeToLog(logBuffer);
  }
  /** 
 * @see LogReadable#readFromLog
 */
  public void readFromLog(  ByteBuffer itemBuffer,  byte entryTypeVersion) throws LogException {
    deletedNodeId=LogUtils.readLong(itemBuffer);
    deletedMainKey=LogUtils.readByteArray(itemBuffer);
    deletedDupKey=LogUtils.readByteArray(itemBuffer);
    dbId.readFromLog(itemBuffer,entryTypeVersion);
  }
  /** 
 * @see LogReadable#dumpLog
 */
  public void dumpLog(  StringBuffer sb,  boolean verbose){
    sb.append("<INDupDeleteEntry node=\"").append(deletedNodeId);
    sb.append("\">");
    sb.append(Key.dumpString(deletedMainKey,0));
    sb.append(Key.dumpString(deletedDupKey,0));
    dbId.dumpLog(sb,verbose);
    sb.append("</INDupDeleteEntry>");
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
