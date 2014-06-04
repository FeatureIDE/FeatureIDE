package com.sleepycat.je.txn;
import com.sleepycat.je.latch.Latch;
import com.sleepycat.je.latch.LatchSupport;
public class TxnManager {
  private Latch allTxnLatch;
  protected void hook821(  EnvironmentImpl env) throws DatabaseException {
    allTxnLatch=LatchSupport.makeLatch(DEBUG_NAME,env);
    original(env);
  }
  protected void hook822(  EnvironmentImpl env) throws DatabaseException {
    if (EnvironmentImpl.getFairLatches()) {
      lockManager=new LatchedLockManager(env);
    }
 else {
      original(env);
    }
  }
  /** 
 * Called when txn is created.
 */
  void registerTxn(  Txn txn) throws DatabaseException {
    allTxnLatch.acquire();
    original(txn);
    allTxnLatch.release();
  }
  /** 
 * Called when txn ends.
 */
  void unRegisterTxn(  Txn txn,  boolean isCommit) throws DatabaseException {
    allTxnLatch.acquire();
    try {
      original(txn,isCommit);
    }
  finally {
      allTxnLatch.release();
    }
  }
  protected long hook823(  long firstActive) throws DatabaseException {
    allTxnLatch.acquire();
    try {
      firstActive=original(firstActive);
    }
  finally {
      allTxnLatch.release();
    }
    return firstActive;
  }
}
