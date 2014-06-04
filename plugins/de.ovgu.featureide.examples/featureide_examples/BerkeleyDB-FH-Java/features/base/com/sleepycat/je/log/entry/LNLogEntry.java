package com.sleepycat.je.log.entry;
import java.nio.ByteBuffer;
import com.sleepycat.je.DatabaseException;
import com.sleepycat.je.dbi.DatabaseId;
import com.sleepycat.je.log.LogEntryType;
import com.sleepycat.je.log.LogUtils;
import com.sleepycat.je.log.LoggableObject;
import com.sleepycat.je.tree.Key;
import com.sleepycat.je.tree.LN;
import com.sleepycat.je.txn.Txn;
import com.sleepycat.je.utilint.DbLsn;
import de.ovgu.cide.jakutil.*;
/** 
 * LNLogEntry embodies all LN transactional log entries.
 * These entries contain:
 * <pre>
 * ln
 * databaseid
 * key            
 * abortLsn       -- if transactional
 * abortKnownDeleted -- if transactional
 * txn            -- if transactional
 * </pre>
 */
public class LNLogEntry implements LogEntry, LoggableObject, NodeLogEntry {
  private LN ln;
  private DatabaseId dbId;
  private byte[] key;
  private long abortLsn=DbLsn.NULL_LSN;
  private boolean abortKnownDeleted;
  private Txn txn;
  private static final byte ABORT_KNOWN_DELETED_MASK=(byte)1;
  private Class logClass;
  private LogEntryType entryType;
  private long nodeId;
  private boolean isTransactional;
  public LNLogEntry(  Class logClass,  boolean isTransactional){
    this.logClass=logClass;
    this.isTransactional=isTransactional;
  }
  public LNLogEntry(  LogEntryType entryType,  LN ln,  DatabaseId dbId,  byte[] key,  long abortLsn,  boolean abortKnownDeleted,  Txn txn){
    this.entryType=entryType;
    this.ln=ln;
    this.dbId=dbId;
    this.key=key;
    this.abortLsn=abortLsn;
    this.abortKnownDeleted=abortKnownDeleted;
    this.txn=txn;
    this.isTransactional=(txn != null);
    this.logClass=ln.getClass();
    this.nodeId=ln.getNodeId();
  }
  /** 
 * @see LogEntry#readEntry
 */
  public void readEntry(  ByteBuffer entryBuffer,  int entrySize,  byte entryTypeVersion,  boolean readFullItem) throws DatabaseException {
    try {
      if (readFullItem) {
        ln=(LN)logClass.newInstance();
        ln.readFromLog(entryBuffer,entryTypeVersion);
        nodeId=ln.getNodeId();
        dbId=new DatabaseId();
        dbId.readFromLog(entryBuffer,entryTypeVersion);
        key=LogUtils.readByteArray(entryBuffer);
        if (isTransactional) {
          abortLsn=LogUtils.readLong(entryBuffer);
          if (DbLsn.getFileNumber(abortLsn) == DbLsn.getFileNumber(DbLsn.NULL_LSN)) {
            abortLsn=DbLsn.NULL_LSN;
          }
          abortKnownDeleted=((entryBuffer.get() & ABORT_KNOWN_DELETED_MASK) != 0) ? true : false;
          txn=new Txn();
          txn.readFromLog(entryBuffer,entryTypeVersion);
        }
      }
 else {
        int endPosition=entryBuffer.position() + entrySize;
        nodeId=LogUtils.readLong(entryBuffer);
        entryBuffer.position(endPosition);
        ln=null;
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
 * @see LogEntry#dumpEntry
 */
  public StringBuffer dumpEntry(  StringBuffer sb,  boolean verbose){
    ln.dumpLog(sb,verbose);
    dbId.dumpLog(sb,verbose);
    sb.append(Key.dumpString(key,0));
    if (isTransactional) {
      if (abortLsn != DbLsn.NULL_LSN) {
        sb.append(DbLsn.toString(abortLsn));
      }
      sb.append("<knownDeleted val=\"");
      sb.append(abortKnownDeleted ? "true" : "false");
      sb.append("\"/>");
      txn.dumpLog(sb,verbose);
    }
    return sb;
  }
  /** 
 * @see LogEntry#getMainItem
 */
  public Object getMainItem(){
    return ln;
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
    return isTransactional;
  }
  /** 
 * @see LogEntry#getTransactionId
 */
  public long getTransactionId(){
    if (isTransactional) {
      return txn.getId();
    }
 else {
      return 0;
    }
  }
  /** 
 * @see NodeLogEntry#getNodeId
 */
  public long getNodeId(){
    return nodeId;
  }
  /** 
 * @see LoggableObject#getLogType
 */
  public LogEntryType getLogType(){
    return entryType;
  }
  /** 
 * @see LoggableObject#marshallOutsideWriteLatchAsk the ln if it can be marshalled outside the log write latch.
 */
  public boolean marshallOutsideWriteLatch(){
    return ln.marshallOutsideWriteLatch();
  }
  /** 
 * Returns true for a deleted LN to count it immediately as obsolete.
 * @see LoggableObject#countAsObsoleteWhenLogged
 */
  public boolean countAsObsoleteWhenLogged(){
    return ln.isDeleted();
  }
  /** 
 * For LN entries, we need to record the latest LSN for that node with the
 * owning transaction, within the protection of the log latch. This is a
 * callback for the log manager to do that recording.
 * @see LoggableObject#postLogWork
 */
  public void postLogWork(  long justLoggedLsn) throws DatabaseException {
    if (isTransactional) {
      txn.addLogInfo(justLoggedLsn);
    }
  }
  /** 
 * @see LoggableObject#getLogSize
 */
  public int getLogSize(){
    int size=ln.getLogSize() + dbId.getLogSize() + LogUtils.getByteArrayLogSize(key);
    if (isTransactional) {
      size+=LogUtils.getLongLogSize();
      size++;
      size+=txn.getLogSize();
    }
    return size;
  }
  /** 
 * @see LoggableObject#writeToLog
 */
  public void writeToLog(  ByteBuffer destBuffer){
    ln.writeToLog(destBuffer);
    dbId.writeToLog(destBuffer);
    LogUtils.writeByteArray(destBuffer,key);
    if (isTransactional) {
      LogUtils.writeLong(destBuffer,abortLsn);
      byte aKD=0;
      if (abortKnownDeleted) {
        aKD|=ABORT_KNOWN_DELETED_MASK;
      }
      destBuffer.put(aKD);
      txn.writeToLog(destBuffer);
    }
  }
  public LN getLN(){
    return ln;
  }
  public DatabaseId getDbId(){
    return dbId;
  }
  public byte[] getKey(){
    return key;
  }
  public byte[] getDupKey(){
    if (ln.isDeleted()) {
      return null;
    }
 else {
      return ln.getData();
    }
  }
  public long getAbortLsn(){
    return abortLsn;
  }
  public boolean getAbortKnownDeleted(){
    return abortKnownDeleted;
  }
  public Long getTxnId(){
    if (isTransactional) {
      return new Long(txn.getId());
    }
 else {
      return null;
    }
  }
  public Txn getUserTxn(){
    if (isTransactional) {
      return txn;
    }
 else {
      return null;
    }
  }
}
