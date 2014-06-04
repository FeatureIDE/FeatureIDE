package com.sleepycat.je.utilint;
import com.sleepycat.je.latch.Latch;
import com.sleepycat.je.latch.LatchSupport;
public abstract class DaemonThread {
  protected Latch workQueueLatch;
  protected void hook856(  String name,  EnvironmentImpl env){
    workQueueLatch=LatchSupport.makeLatch(name + " work queue",env);
    original(name,env);
  }
  public void addToQueue(  Object o) throws DatabaseException {
    workQueueLatch.acquire();
    original(o);
    workQueueLatch.release();
  }
  public int getQueueSize() throws DatabaseException {
    workQueueLatch.acquire();
    int result=original();
    workQueueLatch.release();
    return result;
  }
  protected void hook857() throws InterruptedException, Exception {
    workQueueLatch.release();
    original();
  }
  protected void hook858() throws InterruptedException, Exception {
    workQueueLatch.acquire();
    original();
  }
}
