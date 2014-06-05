package com.sleepycat.je.latch;
import com.sleepycat.je.DatabaseException;
import com.sleepycat.je.RunRecoveryException;
import de.ovgu.cide.jakutil.*;
/** 
 * Simple thread-based non-transactional reader-writer/shared-exclusive latch.
 * Latches provide simple exclusive or shared transient locks on objects.
 * Latches are expected to be held for short, defined periods of time.  No
 * deadlock detection is provided so it is the caller's responsibility to
 * sequence latch acquisition in an ordered fashion to avoid deadlocks.
 */
public interface SharedLatch {
  /** 
 * Set the latch name, used for latches in objects instantiated from the
 * log.
 */
  public void setName(  String name);
  /** 
 * Indicate whether this latch should be tracked in the debugging
 * LatchSupport.latchTable.
 */
  public void setNoteLatch(  boolean noteLatch);
  /** 
 * Acquire a latch for exclusive/write access.  If the thread already holds
 * the latch for shared access, it cannot be upgraded and LatchException
 * will be thrown.
 * Wait for the latch if some other thread is holding it.  If there are
 * threads waiting for access, they will be granted the latch on a FIFO
 * basis if fair latches are enabled.  When the method returns, the latch
 * is held for exclusive access.
 * @throws LatchException if the latch is already held by the current
 * thread for shared access.
 */
  public void acquireExclusive() throws DatabaseException ;
  /** 
 * Probe a latch for exclusive access, but don't block if it's not
 * available.
 * @return true if the latch was acquired, false if it is not available.
 * @throws LatchException if the latch is already held by the calling
 * thread.
 */
  public boolean acquireExclusiveNoWait() throws DatabaseException ;
  /** 
 * Acquire a latch for shared/read access.  Nesting is allowed, that is,
 * the latch may be acquired more than once by the same thread.
 * @throws RunRecoveryException if an InterruptedException exception
 * occurs.
 */
  public void acquireShared() throws DatabaseException ;
  /** 
 * Release an exclusive or shared latch.  If there are other thread(s)
 * waiting for the latch, they are woken up and granted the latch.
 */
  public void release() throws LatchNotHeldException ;
  public boolean isWriteLockedByCurrentThread();
}
