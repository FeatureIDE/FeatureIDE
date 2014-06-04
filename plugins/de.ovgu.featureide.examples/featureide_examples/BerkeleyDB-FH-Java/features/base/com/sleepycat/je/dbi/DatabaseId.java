package com.sleepycat.je.dbi;
import java.io.UnsupportedEncodingException;
import java.nio.ByteBuffer;
import com.sleepycat.je.DatabaseException;
import com.sleepycat.je.log.LogReadable;
import com.sleepycat.je.log.LogUtils;
import com.sleepycat.je.log.LogWritable;
import de.ovgu.cide.jakutil.*;
/** 
 * DatabaseImpl Ids are wrapped in a class so they can be logged.
 */
public class DatabaseId implements Comparable, LogWritable, LogReadable {
  /** 
 * The unique id of this database.
 */
  private int id;
  /** 
 */
  public DatabaseId(  int id){
    this.id=id;
  }
  /** 
 * Uninitialized database id, for logging.
 */
  public DatabaseId(){
  }
  /** 
 * @return id value
 */
  public int getId(){
    return id;
  }
  /** 
 * @return id as bytes, for use as a key
 */
  public byte[] getBytes() throws DatabaseException {
    try {
      return toString().getBytes("UTF-8");
    }
 catch (    UnsupportedEncodingException UEE) {
      throw new DatabaseException(UEE);
    }
  }
  /** 
 * Compare two DatabaseImpl Id's.
 */
  public boolean equals(  Object obj){
    if (this == obj) {
      return true;
    }
    if (!(obj instanceof DatabaseId)) {
      return false;
    }
    return ((DatabaseId)obj).id == id;
  }
  public int hashCode(){
    return id;
  }
  public String toString(){
    return Integer.toString(id);
  }
  /** 
 * see Comparable#compareTo
 */
  public int compareTo(  Object o){
    if (o == null) {
      throw new NullPointerException();
    }
    DatabaseId argId=(DatabaseId)o;
    if (id == argId.id) {
      return 0;
    }
 else     if (id > argId.id) {
      return 1;
    }
 else {
      return -1;
    }
  }
  /** 
 * @see LogWritable#getLogSize
 */
  public int getLogSize(){
    return LogUtils.getIntLogSize();
  }
  /** 
 * @see LogWritable#writeToLog
 */
  public void writeToLog(  ByteBuffer logBuffer){
    LogUtils.writeInt(logBuffer,id);
  }
  /** 
 * @see LogReadable#readFromLog
 */
  public void readFromLog(  ByteBuffer itemBuffer,  byte entryTypeVersion){
    id=LogUtils.readInt(itemBuffer);
  }
  /** 
 * @see LogReadable#dumpLog
 */
  public void dumpLog(  StringBuffer sb,  boolean verbose){
    sb.append("<dbId id=\"");
    sb.append(id);
    sb.append("\"/>");
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
