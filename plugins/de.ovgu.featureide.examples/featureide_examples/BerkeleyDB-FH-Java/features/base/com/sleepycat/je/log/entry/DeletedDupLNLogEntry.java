package com.sleepycat.je.log.entry;
import java.nio.ByteBuffer;
import com.sleepycat.je.DatabaseException;
import com.sleepycat.je.dbi.DatabaseId;
import com.sleepycat.je.log.LogEntryType;
import com.sleepycat.je.log.LogUtils;
import com.sleepycat.je.tree.Key;
import com.sleepycat.je.tree.LN;
import com.sleepycat.je.txn.Txn;
import de.ovgu.cide.jakutil.*;
/** 
 * DupDeletedLNEntry encapsulates a deleted dupe LN entry. This contains all
 * the regular transactional LN log entry fields and an extra key, which is the
 * nulled out data field of the LN (which becomes the key in the duplicate
 * tree.
 */
public class DeletedDupLNLogEntry extends LNLogEntry {
  private byte[] dataAsKey;
  /** 
 * Constructor to read an entry.
 */
  public DeletedDupLNLogEntry(  boolean isTransactional){
    super(com.sleepycat.je.tree.LN.class,isTransactional);
  }
  /** 
 * Constructor to make an object that can write this entry.
 */
  public DeletedDupLNLogEntry(  LogEntryType entryType,  LN ln,  DatabaseId dbId,  byte[] key,  byte[] dataAsKey,  long abortLsn,  boolean abortKnownDeleted,  Txn txn){
    super(entryType,ln,dbId,key,abortLsn,abortKnownDeleted,txn);
    this.dataAsKey=dataAsKey;
  }
  /** 
 * Extends its super class to read in the extra dup key.
 * @see LNLogEntry#readEntry
 */
  public void readEntry(  ByteBuffer entryBuffer,  int entrySize,  byte entryTypeVersion,  boolean readFullItem) throws DatabaseException {
    super.readEntry(entryBuffer,entrySize,entryTypeVersion,readFullItem);
    if (readFullItem) {
      dataAsKey=LogUtils.readByteArray(entryBuffer);
    }
 else {
      dataAsKey=null;
    }
  }
  /** 
 * Extends super class to dump out extra key.
 * @see LNLogEntry#dumpEntry
 */
  public StringBuffer dumpEntry(  StringBuffer sb,  boolean verbose){
    super.dumpEntry(sb,verbose);
    sb.append(Key.dumpString(dataAsKey,0));
    return sb;
  }
  /** 
 * Extend super class to add in extra key.
 * @see LNLogEntry#getLogSize
 */
  public int getLogSize(){
    return super.getLogSize() + LogUtils.getByteArrayLogSize(dataAsKey);
  }
  /** 
 * @see LNLogEntry#writeToLog
 */
  public void writeToLog(  ByteBuffer destBuffer){
    super.writeToLog(destBuffer);
    LogUtils.writeByteArray(destBuffer,dataAsKey);
  }
  /** 
 * Get the data-as-key out of the entry.
 */
  public byte[] getDupKey(){
    return dataAsKey;
  }
}
