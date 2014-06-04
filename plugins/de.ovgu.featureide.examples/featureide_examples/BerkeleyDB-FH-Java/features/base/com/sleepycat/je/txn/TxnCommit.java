package com.sleepycat.je.txn;
import com.sleepycat.je.log.LogEntryType;
import de.ovgu.cide.jakutil.*;
/** 
 * This class writes out a transaction commit or transaction end record.
 */
public class TxnCommit extends TxnEnd {
  public TxnCommit(  long id,  long lastLsn){
    super(id,lastLsn);
  }
  /** 
 * For constructing from the log.
 */
  public TxnCommit(){
  }
  /** 
 * @see TxnEnd#getLogType
 */
  public LogEntryType getLogType(){
    return LogEntryType.LOG_TXN_COMMIT;
  }
  protected String getTagName(){
    return "TxnCommit";
  }
}
