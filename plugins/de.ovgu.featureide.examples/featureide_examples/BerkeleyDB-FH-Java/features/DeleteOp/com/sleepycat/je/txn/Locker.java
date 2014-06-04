package com.sleepycat.je.txn;
public abstract class Locker {
  /** 
 * Database operations like remove and truncate leave behind
 * residual DatabaseImpls that must be purged at transaction
 * commit or abort. 
 */
  public abstract void markDeleteAtTxnEnd(  DatabaseImpl db,  boolean deleteAtCommit) throws DatabaseException ;
}
