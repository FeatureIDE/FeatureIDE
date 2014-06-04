package com.sleepycat.je.txn;
import com.sleepycat.je.DatabaseException;
import com.sleepycat.je.dbi.EnvironmentImpl;
import de.ovgu.cide.jakutil.*;
/** 
 * Extends BasicLocker to share locks with another specific locker.
 * <p>In general, a BuddyLocker can be used whenever the primary (API) locker
 * is in use, and we need to lock a node and release that lock before the
 * primary locker transaction ends.  In other words, for this particular lock
 * we don't want to use two-phase locking.  To accomplish that we use a
 * separate BuddyLocker instance to hold the lock, while sharing locks with the
 * primary locker.  The BuddyLocker can be closed to release this particular
 * lock, without releasing the other locks held by the primary locker.</p>
 * <p>In particular, a BuddyLocker is used when acquiring a RANGE_INSERT lock.
 * RANGE_INSERT only needs to be held until the point we have inserted the new
 * node into the BIN.  A separate locker is therefore used so we can release
 * that lock separately when the insertion into the BIN is complete.  But the
 * RANGE_INSERT lock must not conflict with locks held by the primary locker.
 * So a BuddyLocker is used that shares locks with the primary locker.</p>
 */
public class BuddyLocker extends BasicLocker {
  private Locker buddy;
  /** 
 * Creates a BuddyLocker.
 */
  public BuddyLocker(  EnvironmentImpl env,  Locker buddy) throws DatabaseException {
    super(env);
    this.buddy=buddy;
  }
  /** 
 * Returns the buddy locker.
 */
  Locker getBuddy(){
    return buddy;
  }
  /** 
 * Forwards this call to the buddy locker.
 */
  public Txn getTxnLocker(){
    return buddy.getTxnLocker();
  }
  /** 
 * Creates a new instance of this txn for the same environment.  No
 * transactional locks are held by this object, so no locks are retained.
 * newNonTxnLocker is also called for the BuddyLocker.
 */
  public Locker newNonTxnLocker() throws DatabaseException {
    return new BuddyLocker(envImpl,buddy.newNonTxnLocker());
  }
  /** 
 * Forwards this call to the base class and to the buddy locker.
 */
  public void releaseNonTxnLocks() throws DatabaseException {
    super.releaseNonTxnLocks();
    buddy.releaseNonTxnLocks();
  }
  /** 
 * Returns whether this locker can share locks with the given locker.
 */
  public boolean sharesLocksWith(  Locker other){
    if (super.sharesLocksWith(other)) {
      return true;
    }
 else {
      return buddy == other;
    }
  }
}
