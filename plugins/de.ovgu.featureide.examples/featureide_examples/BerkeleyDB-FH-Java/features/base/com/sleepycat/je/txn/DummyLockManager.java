package com.sleepycat.je.txn;
import java.util.Set;
import com.sleepycat.je.DatabaseException;
import com.sleepycat.je.LockStats;
import com.sleepycat.je.dbi.DatabaseImpl;
import com.sleepycat.je.dbi.EnvironmentImpl;
import com.sleepycat.je.dbi.MemoryBudget;
import de.ovgu.cide.jakutil.*;
/** 
 * DummyLockManager performs no locking for DS mode.
 */
public class DummyLockManager extends LockManager {
  public DummyLockManager(  EnvironmentImpl envImpl) throws DatabaseException {
    super(envImpl);
  }
  /** 
 * @see LockManager#attemptLock
 */
  protected LockAttemptResult attemptLock(  Long nodeId,  Locker locker,  LockType type,  boolean nonBlockingRequest) throws DatabaseException {
    return new LockAttemptResult(null,LockGrantType.NEW,true);
  }
  /** 
 * @see LockManager#makeTimeoutMsg
 */
  protected String makeTimeoutMsg(  String lockOrTxn,  Locker locker,  long nodeId,  LockType type,  LockGrantType grantType,  Lock useLock,  long timeout,  long start,  long now,  DatabaseImpl database){
    return null;
  }
  /** 
 * @see LockManager#releaseAndNotifyTargets
 */
  protected Set releaseAndFindNotifyTargets(  long nodeId,  Lock lock,  Locker locker,  boolean removeFromLocker) throws DatabaseException {
    return null;
  }
  /** 
 * @see LockManager#transfer
 */
  void transfer(  long nodeId,  Locker owningLocker,  Locker destLocker,  boolean demoteToRead) throws DatabaseException {
  }
  /** 
 * @see LockManager#transferMultiple
 */
  void transferMultiple(  long nodeId,  Locker owningLocker,  Locker[] destLockers) throws DatabaseException {
  }
  /** 
 * @see LockManager#demote
 */
  void demote(  long nodeId,  Locker locker) throws DatabaseException {
  }
  /** 
 * @see LockManager#isLocked
 */
  boolean isLocked(  Long nodeId){
    return false;
  }
  /** 
 * @see LockManager#isOwner
 */
  boolean isOwner(  Long nodeId,  Locker locker,  LockType type){
    return false;
  }
  /** 
 * @see LockManager#isWaiter
 */
  boolean isWaiter(  Long nodeId,  Locker locker){
    return false;
  }
  /** 
 * @see LockManager#nWaiters
 */
  int nWaiters(  Long nodeId){
    return 0;
  }
  /** 
 * @see LockManager#nOwners
 */
  int nOwners(  Long nodeId){
    return 0;
  }
  /** 
 * @see LockManager#getWriterOwnerLocker
 */
  Locker getWriteOwnerLocker(  Long nodeId) throws DatabaseException {
    return null;
  }
  /** 
 * @see LockManager#validateOwnership
 */
  protected boolean validateOwnership(  Long nodeId,  Locker locker,  LockType type,  boolean flushFromWaiters,  MemoryBudget mb) throws DatabaseException {
    return true;
  }
  /** 
 * @see LockManager#dumpLockTable
 */
  protected void dumpLockTable(  LockStats stats) throws DatabaseException {
  }
}
