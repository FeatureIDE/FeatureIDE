package com.sleepycat.je.latch;
class Java5LatchImpl {
  private LatchStats stats=new LatchStats();
  /** 
 * @return a LatchStats object with information about this latch.
 */
  public LatchStats getLatchStats(){
    LatchStats s=null;
    try {
      s=(LatchStats)stats.clone();
    }
 catch (    CloneNotSupportedException e) {
    }
    return s;
  }
  protected void hook416() throws DatabaseException {
    if (lock.isLocked()) {
      stats.nAcquiresWithContention++;
    }
 else {
      stats.nAcquiresNoWaiters++;
    }
    original();
  }
  protected void hook417() throws DatabaseException {
    stats.nAcquiresSelfOwned++;
    original();
  }
  protected void hook418() throws LatchException {
    stats.nAcquiresSelfOwned++;
    original();
  }
  protected void hook419() throws LatchException {
    stats.nAcquireNoWaitSuccessful++;
    original();
  }
  protected void hook420() throws LatchException {
    stats.nAcquireNoWaitUnsuccessful++;
    original();
  }
  protected void hook421() throws IllegalMonitorStateException {
    stats.nReleases++;
    original();
  }
}
