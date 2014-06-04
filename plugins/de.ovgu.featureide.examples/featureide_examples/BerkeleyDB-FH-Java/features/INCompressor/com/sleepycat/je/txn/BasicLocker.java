package com.sleepycat.je.txn;
public class BasicLocker {
  /** 
 * Release locks at the end of the transaction.
 */
  public void operationEnd(  boolean operationOK) throws DatabaseException {
    original(operationOK);
synchronized (this) {
      if ((deleteInfo != null) && (deleteInfo.size() > 0)) {
        envImpl.addToCompressorQueue(deleteInfo.values(),false);
        deleteInfo.clear();
      }
    }
  }
}
