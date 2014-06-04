package com.sleepycat.je.txn;
import com.sleepycat.je.Database;
import com.sleepycat.je.DatabaseException;
import com.sleepycat.je.TransactionConfig;
import com.sleepycat.je.dbi.EnvironmentImpl;
import de.ovgu.cide.jakutil.*;
/** 
 * An AutoTxn is one that's created by use of the AutoCommit property.
 */
public class AutoTxn extends Txn {
  public AutoTxn(  EnvironmentImpl env,  TransactionConfig config) throws DatabaseException {
    super(env,config);
  }
  /** 
 * AutoTxns abort or commit at the end of the operation
 */
  public void operationEnd(  boolean operationOK) throws DatabaseException {
    if (operationOK) {
      commit();
    }
 else {
      abort(false);
    }
  }
  /** 
 * AutoTxns abort or commit at the end of the operation
 */
  public void operationEnd() throws DatabaseException {
    operationEnd(true);
  }
  /** 
 * Transfer any handle locks to the db handle on success.
 * On failure, leave it with this txn, the handle lock will
 * be released at abort and the handle marked invalid.
 */
  public void setHandleLockOwner(  boolean operationOK,  Database dbHandle,  boolean dbIsClosing) throws DatabaseException {
    if (operationOK) {
      if (!dbIsClosing) {
        transferHandleLockToHandle(dbHandle);
      }
      unregisterHandle(dbHandle);
    }
  }
}
