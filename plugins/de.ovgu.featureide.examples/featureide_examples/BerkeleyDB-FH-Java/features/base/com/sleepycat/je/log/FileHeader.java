package com.sleepycat.je.log;
import java.nio.ByteBuffer;
import java.sql.Timestamp;
import java.util.Calendar;
import com.sleepycat.je.DatabaseException;
import de.ovgu.cide.jakutil.*;
/** 
 * A FileHeader embodies the header information at the beginning of each log
 * file.
 */
public class FileHeader implements LoggableObject, LogReadable {
  private static final int LOG_VERSION=3;
  private long fileNum;
  private long lastEntryInPrevFileOffset;
  private Timestamp time;
  private int logVersion;
  FileHeader(  long fileNum,  long lastEntryInPrevFileOffset){
    this.fileNum=fileNum;
    this.lastEntryInPrevFileOffset=lastEntryInPrevFileOffset;
    Calendar now=Calendar.getInstance();
    time=new Timestamp(now.getTimeInMillis());
    logVersion=LOG_VERSION;
  }
  /** 
 * For logging only.
 */
  public FileHeader(){
  }
  /** 
 * @return whether the file header has an old version number.
 * @throws DatabaseException if the header isn't valid.
 */
  boolean validate(  String fileName,  long expectedFileNum) throws DatabaseException {
    if (fileNum != expectedFileNum) {
      throw new LogException("Wrong filenum in header for file " + fileName + " expected "+ expectedFileNum+ " got "+ fileNum);
    }
    return logVersion < LOG_VERSION;
  }
  /** 
 * @return the offset of the last entry in the previous file.
 */
  long getLastEntryInPrevFileOffset(){
    return lastEntryInPrevFileOffset;
  }
  /** 
 * @see LoggableObject#getLogType
 */
  public LogEntryType getLogType(){
    return LogEntryType.LOG_FILE_HEADER;
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
  public void postLogWork(  long justLoggedLsn) throws DatabaseException {
  }
  /** 
 * A header is always a known size.
 */
  static int entrySize(){
    return LogUtils.getTimestampLogSize() + LogUtils.UNSIGNED_INT_BYTES + LogUtils.LONG_BYTES+ LogUtils.INT_BYTES;
  }
  /** 
 * @see LoggableObject#getLogSize
 * @return number of bytes used to store this object
 */
  public int getLogSize(){
    return entrySize();
  }
  /** 
 * @see LoggableObject#writeToLogSerialize this object into the buffer. Update cksum with all
 * the bytes used by this object
 * @param logBuffer is the destination buffer
 */
  public void writeToLog(  ByteBuffer logBuffer){
    LogUtils.writeTimestamp(logBuffer,time);
    LogUtils.writeUnsignedInt(logBuffer,fileNum);
    LogUtils.writeLong(logBuffer,lastEntryInPrevFileOffset);
    LogUtils.writeInt(logBuffer,logVersion);
  }
  /** 
 * @see LogReadable#readFromLogInitialize this object from the data in itemBuf.
 * @param itemBuf the source buffer
 */
  public void readFromLog(  ByteBuffer logBuffer,  byte entryTypeVersion) throws LogException {
    time=LogUtils.readTimestamp(logBuffer);
    fileNum=LogUtils.getUnsignedInt(logBuffer);
    lastEntryInPrevFileOffset=LogUtils.readLong(logBuffer);
    logVersion=LogUtils.readInt(logBuffer);
    if (logVersion > LOG_VERSION) {
      throw new LogException("Expected log version " + LOG_VERSION + " or earlier but found "+ logVersion+ " -- this version is not supported.");
    }
  }
  /** 
 * @see LogReadable#dumpLog
 * @param sb destination string buffer
 * @param verbose if true, dump the full, verbose version
 */
  public void dumpLog(  StringBuffer sb,  boolean verbose){
    sb.append("<FileHeader num=\"0x");
    sb.append(Long.toHexString(fileNum));
    sb.append("\" lastEntryInPrevFileOffset=\"0x");
    sb.append(Long.toHexString(lastEntryInPrevFileOffset));
    sb.append("\" logVersion=\"0x");
    sb.append(Integer.toHexString(logVersion));
    sb.append("\" time=\"").append(time);
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
  /** 
 * Print in xml format
 */
  public String toString(){
    StringBuffer sb=new StringBuffer();
    dumpLog(sb,true);
    return sb.toString();
  }
}
