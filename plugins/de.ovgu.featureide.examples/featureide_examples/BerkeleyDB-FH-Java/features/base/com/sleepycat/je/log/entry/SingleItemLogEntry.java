package com.sleepycat.je.log.entry;
import java.nio.ByteBuffer;
import com.sleepycat.je.DatabaseException;
import com.sleepycat.je.log.LogReadable;
import de.ovgu.cide.jakutil.*;
/** 
 * This class embodies log entries that have a single loggable item.
 */
public class SingleItemLogEntry implements LogEntry {
  private Class logClass;
  LogReadable item;
  public SingleItemLogEntry(  Class logClass){
    this.logClass=logClass;
  }
  /** 
 * @see LogEntry#readEntry
 */
  public void readEntry(  ByteBuffer entryBuffer,  int entrySize,  byte entryTypeVersion,  boolean readFullItem) throws DatabaseException {
    try {
      item=(LogReadable)logClass.newInstance();
      item.readFromLog(entryBuffer,entryTypeVersion);
    }
 catch (    IllegalAccessException e) {
      throw new DatabaseException(e);
    }
catch (    InstantiationException e) {
      throw new DatabaseException(e);
    }
  }
  /** 
 * @see LogEntry#dumpEntry
 */
  public StringBuffer dumpEntry(  StringBuffer sb,  boolean verbose){
    item.dumpLog(sb,verbose);
    return sb;
  }
  /** 
 * @see LogEntry#getMainItem
 */
  public Object getMainItem(){
    return item;
  }
  /** 
 * @see LogEntry#clone
 */
  public Object clone() throws CloneNotSupportedException {
    return super.clone();
  }
  /** 
 * @see LogEntry#isTransactional
 */
  public boolean isTransactional(){
    return item.logEntryIsTransactional();
  }
  /** 
 * @see LogEntry#getTransactionId
 */
  public long getTransactionId(){
    return item.getTransactionId();
  }
  /** 
 * @return a new instance
 */
  public LogEntry getNewInstance() throws DatabaseException {
    try {
      return (LogEntry)logClass.newInstance();
    }
 catch (    InstantiationException e) {
      throw new DatabaseException(e);
    }
catch (    IllegalAccessException e) {
      throw new DatabaseException(e);
    }
  }
}
