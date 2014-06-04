package com.sleepycat.je.latch;
public class SharedLatchImpl {
  private LatchStats stats=new LatchStats();
  protected void hook429() throws DatabaseException, InterruptedException {
    stats.nAcquiresNoWaiters++;
    original();
  }
  protected void hook430() throws DatabaseException, InterruptedException {
    stats.nAcquiresWithContention++;
    original();
  }
  protected void hook431() throws DatabaseException {
    stats.nAcquiresNoWaiters++;
    original();
  }
  protected void hook432() throws DatabaseException, InterruptedException {
    stats.nAcquireSharedSuccessful++;
    original();
  }
  protected void hook433() throws LatchNotHeldException {
    stats.nReleases++;
    original();
  }
}
