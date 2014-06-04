package com.sleepycat.je.txn;
public abstract class Locker {
  /** 
 * Get lock count, for per transaction lock stats, for internal debugging.
 */
  public abstract LockStats collectStats(  LockStats stats) throws DatabaseException ;
}
