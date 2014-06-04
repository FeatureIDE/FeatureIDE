package com.sleepycat.je.log.entry;
import java.nio.ByteBuffer;
import com.sleepycat.je.DatabaseException;
import com.sleepycat.je.dbi.DatabaseId;
import com.sleepycat.je.dbi.EnvironmentImpl;
import com.sleepycat.je.log.LogEntryType;
import com.sleepycat.je.log.LogUtils;
import com.sleepycat.je.log.LoggableObject;
import com.sleepycat.je.tree.IN;
import com.sleepycat.je.utilint.DbLsn;
import de.ovgu.cide.jakutil.*;
/** 
 * INLogEntry embodies all IN log entries.  These entries contain an IN and a
 * databaseId. This class can both write out an entry and read one in.
 */
public class INLogEntry implements LogEntry, LoggableObject, NodeLogEntry, INContainingEntry {
  private IN in;
  private DatabaseId dbId;
  private long obsoleteLsn;
  private long nodeId;
  private Class logClass;
  /** 
 * Construct a log entry for reading.
 */
  public INLogEntry(  Class logClass){
    this.logClass=logClass;
  }
  /** 
 * Construct a log entry for writing to the log.
 */
  public INLogEntry(  IN in){
    this.in=in;
    this.dbId=in.getDatabase().getId();
    this.logClass=in.getClass();
    this.nodeId=in.getNodeId();
    this.obsoleteLsn=in.getLastFullVersion();
  }
  /** 
 * Read in an IN entry.
 */
  public void readEntry(  ByteBuffer entryBuffer,  int entrySize,  byte entryTypeVersion,  boolean readFullItem) throws DatabaseException {
    entryTypeVersion&=LogEntryType.clearProvisional(entryTypeVersion);
    try {
      if (readFullItem) {
        in=(IN)logClass.newInstance();
        in.readFromLog(entryBuffer,entryTypeVersion);
        nodeId=in.getNodeId();
      }
 else {
        int position=entryBuffer.position() + entrySize;
        if (entryTypeVersion == 1) {
          position-=LogUtils.UNSIGNED_INT_BYTES;
        }
 else         if (entryTypeVersion >= 2) {
          position-=LogUtils.LONG_BYTES;
        }
        position-=LogUtils.INT_BYTES;
        nodeId=LogUtils.readLong(entryBuffer);
        entryBuffer.position(position);
        in=null;
      }
      dbId=new DatabaseId();
      dbId.readFromLog(entryBuffer,entryTypeVersion);
      if (entryTypeVersion < 1) {
        obsoleteLsn=DbLsn.NULL_LSN;
      }
 else       if (entryTypeVersion == 1) {
        long fileNum=LogUtils.getUnsignedInt(entryBuffer);
        if (fileNum == 0xffffffffL) {
          obsoleteLsn=DbLsn.NULL_LSN;
        }
 else {
          obsoleteLsn=DbLsn.makeLsn(fileNum,0);
        }
      }
 else {
        obsoleteLsn=LogUtils.readLong(entryBuffer);
      }
    }
 catch (    IllegalAccessException e) {
      throw new DatabaseException(e);
    }
catch (    InstantiationException e) {
      throw new DatabaseException(e);
    }
  }
  /** 
 * Returns the LSN of the prior version of this node.  Used for counting
 * the prior version as obsolete.  If the offset of the LSN is zero, only
 * the file number is known because we read a version 1 log entry.
 */
  public long getObsoleteLsn(){
    return obsoleteLsn;
  }
  /** 
 * Print out the contents of an entry.
 */
  public StringBuffer dumpEntry(  StringBuffer sb,  boolean verbose){
    in.dumpLog(sb,verbose);
    dbId.dumpLog(sb,verbose);
    return sb;
  }
  /** 
 * @return the item in the log entry
 */
  public Object getMainItem(){
    return in;
  }
  public Object clone() throws CloneNotSupportedException {
    return super.clone();
  }
  /** 
 * @see LogEntry#isTransactional
 */
  public boolean isTransactional(){
    return false;
  }
  /** 
 * @see LogEntry#getTransactionId
 */
  public long getTransactionId(){
    return 0;
  }
  /** 
 * @see LoggableObject#getLogType
 */
  public LogEntryType getLogType(){
    return in.getLogType();
  }
  /** 
 * @see LoggableObject#marshallOutsideWriteLatchAsk the in if it can be marshalled outside the log write latch.
 */
  public boolean marshallOutsideWriteLatch(){
    return in.marshallOutsideWriteLatch();
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
    return (in.getLogSize() + dbId.getLogSize() + LogUtils.LONG_BYTES);
  }
  /** 
 * @see LoggableObject#writeToLog
 */
  public void writeToLog(  ByteBuffer destBuffer){
    in.writeToLog(destBuffer);
    dbId.writeToLog(destBuffer);
    LogUtils.writeLong(destBuffer,obsoleteLsn);
  }
  public IN getIN(  EnvironmentImpl env) throws DatabaseException {
    return in;
  }
  /** 
 * @see NodeLogEntry#getNodeId
 */
  public long getNodeId(){
    return nodeId;
  }
  /** 
 * @see INContainingEntry#getDbId()
 */
  public DatabaseId getDbId(){
    return (DatabaseId)dbId;
  }
  /** 
 * @return the LSN that represents this IN. For a vanilla IN entry, it's 
 * the last lsn read by the log reader.
 */
  public long getLsnOfIN(  long lastReadLsn){
    return lastReadLsn;
  }
}
