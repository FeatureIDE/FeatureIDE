package com.sleepycat.je.txn;
import com.sleepycat.je.log.LogEntryType;
import de.ovgu.cide.jakutil.*;
/** 
 * This class writes out a transaction commit or transaction end record.
 */
public class TxnAbort extends TxnEnd {
  public TxnAbort(  long id,  long lastLsn){
    super(id,lastLsn);
  }
  /** 
 * For constructing from the log.
 */
  public TxnAbort(){
  }
  /** 
 * @see TxnEnd#getLogType
 */
  public LogEntryType getLogType(){
    return LogEntryType.LOG_TXN_ABORT;
  }
  protected String getTagName(){
    return "TxnAbort";
  }
}
