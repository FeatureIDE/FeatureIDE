package com.sleepycat.je.latch;
import com.sleepycat.je.DatabaseException;
import com.sleepycat.je.RunRecoveryException;
import de.ovgu.cide.jakutil.*;
public interface Latch {
  /** 
 * Set the latch name, used for latches in objects instantiated from
 * the log.
 */
  public void setName(  String name);
  /** 
 * Acquire a latch for exclusive/write access.
 * <p>Wait for the latch if some other thread is holding it.  If there are
 * threads waiting for access, they will be granted the latch on a FIFO
 * basis.  When the method returns, the latch is held for exclusive
 * access.</p>
 * @throws LatchException if the latch is already held by the calling
 * thread.
 * @throws RunRecoveryException if an InterruptedException exception
 * occurs.
 */
  public void acquire() throws DatabaseException ;
  /** 
 * Acquire a latch for exclusive/write access, but do not block if it's not
 * available.
 * @return true if the latch was acquired, false if it is not available.
 * @throws LatchException if the latch is already held by the calling
 * thread.
 */
  public boolean acquireNoWait() throws LatchException ;
  /** 
 * Release the latch.  If there are other thread(s) waiting for the latch,
 * one is woken up and granted the latch. If the latch was not owned by 
 * the caller, just return;
 */
  public void releaseIfOwner();
  /** 
 * Release the latch.  If there are other thread(s) waiting for the latch,
 * they are woken up and granted the latch.
 * @throws LatchNotHeldException if the latch is not currently held.
 */
  public void release() throws LatchNotHeldException ;
  /** 
 * Return true if the current thread holds this latch.
 * @return true if we hold this latch.  False otherwise.
 */
  public boolean isOwner();
  /** 
 * Used only for unit tests.
 * @return the thread that currently holds the latch for exclusive access.
 */
  public Thread owner();
  /** 
 * Return the number of threads waiting.
 * @return the number of threads waiting for the latch.
 */
  public int nWaiters();
  /** 
 * Formats a latch owner and waiters.
 */
  public String toString();
}
