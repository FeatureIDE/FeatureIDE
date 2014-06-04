package com.sleepycat.je.txn;
import com.sleepycat.je.DatabaseException;
import com.sleepycat.je.dbi.EnvironmentImpl;
import de.ovgu.cide.jakutil.*;
/** 
 * Extends BasicLocker to share locks among all lockers for the same thread.
 * This locker is used when a JE entry point is called with a null transaction
 * parameter.
 */
public class ThreadLocker extends BasicLocker {
  /** 
 * Creates a ThreadLocker.
 */
  public ThreadLocker(  EnvironmentImpl env) throws DatabaseException {
    super(env);
  }
  /** 
 * Check that this txn is not used in the wrong thread.
 */
  protected void checkState(  boolean ignoreCalledByAbort) throws DatabaseException {
    if (thread != Thread.currentThread()) {
      throw new DatabaseException("A per-thread transaction was" + " created in " + thread + " but used in "+ Thread.currentThread());
    }
  }
  /** 
 * Creates a new instance of this txn for the same environment.  No
 * transactional locks are held by this object, so no locks are retained.
 */
  public Locker newNonTxnLocker() throws DatabaseException {
    checkState(false);
    return new ThreadLocker(envImpl);
  }
  /** 
 * Returns whether this locker can share locks with the given locker.
 * Locks are shared when both are txns are ThreadLocker instances for the
 * same thread.
 */
  public boolean sharesLocksWith(  Locker other){
    if (super.sharesLocksWith(other)) {
      return true;
    }
 else     if (other instanceof ThreadLocker) {
      return thread == ((ThreadLocker)other).thread;
    }
 else {
      return false;
    }
  }
}
