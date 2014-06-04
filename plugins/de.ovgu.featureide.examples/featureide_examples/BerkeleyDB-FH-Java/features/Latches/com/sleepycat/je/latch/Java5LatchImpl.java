package com.sleepycat.je.latch;
import java.util.concurrent.locks.ReentrantLock;
import com.sleepycat.je.DatabaseException;
import com.sleepycat.je.dbi.EnvironmentImpl;
import de.ovgu.cide.jakutil.*;
/** 
 * Java5LatchImpl provides an implementation of the Latch interface.  By using
 * a wrapper class we can avoid link errors when we run in Java 1.4 JVMs.
 * LatchSupport.java will only reference this class if it knows that the
 * ReentrantLock class is available at runtime through Class.forName().
 * LatchSupport only references this class through the Latch interface and only
 * constructs an instance using
 * Class.forName("Java5LatchImpl").newInstance();
 */
class Java5LatchImpl implements Latch {
static private class JEReentrantLock extends ReentrantLock {
    JEReentrantLock(    boolean fair){
      super(fair);
    }
    protected Thread getOwner(){
      return super.getOwner();
    }
  }
  private JEReentrantLock lock;
  private String name;
  Java5LatchImpl(){
    lock=new JEReentrantLock(EnvironmentImpl.getFairLatches());
  }
  /** 
 * Set the latch name, used for latches in objects instantiated from
 * the log.
 */
  public void setName(  String name){
    this.name=name;
  }
  /** 
 * Acquire a latch for exclusive/write access.
 * <p>Wait for the latch if some other thread is holding it.  If there are
 * threads waiting for access, they will be granted the latch on a FIFO
 * basis.  When the method returns, the latch is held for exclusive
 * access.</p>
 * @throws LatchException if the latch is already held by the calling
 * thread.
 */
  public void acquire() throws DatabaseException {
    try {
      if (lock.isHeldByCurrentThread()) {
        this.hook417();
        throw new LatchException(name + " already held");
      }
      this.hook416();
      lock.lock();
      assert noteLatch();
    }
  finally {
      assert EnvironmentImpl.maybeForceYield();
    }
  }
  /** 
 * Acquire a latch for exclusive/write access, but do not block if it's not
 * available.
 * @return true if the latch was acquired, false if it is not available.
 * @throws LatchException if the latch is already held by the calling
 * thread.
 */
  public boolean acquireNoWait() throws LatchException {
    try {
      if (lock.isHeldByCurrentThread()) {
        this.hook418();
        throw new LatchException(name + " already held");
      }
      boolean ret=lock.tryLock();
      if (ret) {
        assert noteLatch();
        this.hook419();
      }
 else {
        this.hook420();
      }
      return ret;
    }
  finally {
      assert EnvironmentImpl.maybeForceYield();
    }
  }
  /** 
 * Release the latch.  If there are other thread(s) waiting for the latch,
 * one is woken up and granted the latch. If the latch was not owned by 
 * the caller, just return;
 */
  public void releaseIfOwner(){
    doRelease(false);
  }
  /** 
 * Release the latch.  If there are other thread(s) waiting for the latch,
 * they are woken up and granted the latch.
 * @throws LatchNotHeldException if the latch is not currently held.
 */
  public void release() throws LatchNotHeldException {
    if (doRelease(true)) {
      throw new LatchNotHeldException(name + " not held");
    }
  }
  /** 
 * Do the work of releasing the latch. Wake up any waiters.
 * @returns true if this latch was not owned by the caller.
 */
  private boolean doRelease(  boolean checkHeld){
    try {
      if (!lock.isHeldByCurrentThread()) {
        return true;
      }
      lock.unlock();
      this.hook421();
      assert unNoteLatch(checkHeld);
    }
 catch (    IllegalMonitorStateException IMSE) {
      return true;
    }
    return false;
  }
  /** 
 * Return true if the current thread holds this latch.
 * @return true if we hold this latch.  False otherwise.
 */
  public boolean isOwner(){
    return lock.isHeldByCurrentThread();
  }
  /** 
 * Used only for unit tests.
 * @return the thread that currently holds the latch for exclusive access.
 */
  public Thread owner(){
    return lock.getOwner();
  }
  /** 
 * Return the number of threads waiting.
 * @return the number of threads waiting for the latch.
 */
  public int nWaiters(){
    return lock.getQueueLength();
  }
  /** 
 * Formats a latch owner and waiters.
 */
  public String toString(){
    return lock.toString();
  }
  /** 
 * Only call under the assert system. This records latching by thread.
 */
  private boolean noteLatch() throws LatchException {
    return LatchSupport.latchTable.noteLatch(this);
  }
  /** 
 * Only call under the assert system. This records latching by thread.
 */
  private boolean unNoteLatch(  boolean checkHeld){
    if (checkHeld) {
      return LatchSupport.latchTable.unNoteLatch(this,name);
    }
 else {
      LatchSupport.latchTable.unNoteLatch(this,name);
      return true;
    }
  }
  protected void hook416() throws DatabaseException {
  }
  protected void hook417() throws DatabaseException {
  }
  protected void hook418() throws LatchException {
  }
  protected void hook419() throws LatchException {
  }
  protected void hook420() throws LatchException {
  }
  protected void hook421() throws IllegalMonitorStateException {
  }
}
