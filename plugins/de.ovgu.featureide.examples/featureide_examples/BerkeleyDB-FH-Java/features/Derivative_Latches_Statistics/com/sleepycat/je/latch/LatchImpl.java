package com.sleepycat.je.latch;
public class LatchImpl {
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
  protected void hook422() throws DatabaseException, InterruptedException {
    stats.nAcquiresSelfOwned++;
    original();
  }
  protected void hook423() throws DatabaseException, InterruptedException {
    stats.nAcquiresNoWaiters++;
    original();
  }
  protected void hook424() throws DatabaseException, InterruptedException {
    stats.nAcquiresWithContention++;
    original();
  }
  protected void hook425() throws LatchException {
    stats.nAcquiresSelfOwned++;
    original();
  }
  protected void hook426() throws LatchException {
    stats.nAcquireNoWaitSuccessful++;
    original();
  }
  protected void hook427() throws LatchException {
    stats.nAcquireNoWaitUnsuccessful++;
    original();
  }
  protected void hook428(){
    stats.nReleases++;
    original();
  }
}
