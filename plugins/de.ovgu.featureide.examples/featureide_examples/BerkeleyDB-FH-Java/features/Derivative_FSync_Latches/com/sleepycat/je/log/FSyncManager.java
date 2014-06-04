package com.sleepycat.je.log;
import com.sleepycat.je.latch.Latch;
import com.sleepycat.je.latch.LatchSupport;
class FSyncManager {
  private Latch fsyncLatch;
  protected void hook434(  EnvironmentImpl envImpl) throws DatabaseException {
    fsyncLatch=LatchSupport.makeLatch("fsyncLatch",envImpl);
    original(envImpl);
  }
}
