package com.sleepycat.je.txn;
public class ReadCommittedLocker {
  /** 
 * Forwards this method to the transactional buddy.  The buddy handles
 * write locks and therefore handles delete information.
 */
  public void addDeleteInfo(  BIN bin,  Key deletedKey) throws DatabaseException {
    getBuddy().addDeleteInfo(bin,deletedKey);
  }
}
