package com.sleepycat.je.txn;
import com.sleepycat.je.latch.Latch;
import com.sleepycat.je.latch.LatchSupport;
public abstract class LockManager {
  protected Latch[] lockTableLatches;
  private boolean checkNoLatchesHeld(  boolean nonBlockingRequest){
    if (nonBlockingRequest) {
      return true;
    }
 else {
      return (LatchSupport.countLatchesHeld() == 0);
    }
  }
  protected void hook770() throws DatabaseException {
    lockTableLatches=new Latch[nLockTables];
    original();
  }
  protected void hook771(  EnvironmentImpl envImpl,  int i) throws DatabaseException {
    lockTableLatches[i]=LatchSupport.makeLatch("Lock Table " + i,envImpl);
    original(envImpl,i);
  }
  protected void hook772(  boolean nonBlockingRequest) throws DeadlockException, DatabaseException {
    assert checkNoLatchesHeld(nonBlockingRequest) : LatchSupport.countLatchesHeld() + " latches held while trying to lock, lock table =" + LatchSupport.latchesHeldToString();
    original(nonBlockingRequest);
  }
  protected void hook773(  StringBuffer sb,  int i) throws DatabaseException {
    lockTableLatches[i].acquire();
    try {
      original(sb,i);
    }
  finally {
      lockTableLatches[i].release();
    }
  }
}
