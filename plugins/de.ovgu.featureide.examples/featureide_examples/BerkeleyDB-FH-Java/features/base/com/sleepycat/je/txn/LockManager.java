package com.sleepycat.je.txn;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;
import com.sleepycat.je.DatabaseException;
import com.sleepycat.je.DeadlockException;
import com.sleepycat.je.LockStats;
import com.sleepycat.je.RunRecoveryException;
import com.sleepycat.je.config.EnvironmentParams;
import com.sleepycat.je.dbi.DatabaseImpl;
import com.sleepycat.je.dbi.DbConfigManager;
import com.sleepycat.je.dbi.EnvConfigObserver;
import com.sleepycat.je.dbi.EnvironmentImpl;
import com.sleepycat.je.dbi.MemoryBudget;
import com.sleepycat.je.dbi.RangeRestartException;
import de.ovgu.cide.jakutil.*;
/** 
 * LockManager manages locks.
 * Note that locks are counted as taking up part of the JE cache;
 */
public abstract class LockManager implements EnvConfigObserver {
  protected int nLockTables=1;
  private Map[] lockTables;
  private EnvironmentImpl envImpl;
  private MemoryBudget memoryBudget;
  private static RangeRestartException rangeRestartException=new RangeRestartException();
  private static boolean lockTableDump=false;
  public LockManager(  EnvironmentImpl envImpl) throws DatabaseException {
    DbConfigManager configMgr=envImpl.getConfigManager();
    this.hook779(configMgr);
    lockTables=new Map[nLockTables];
    this.hook770();
    for (int i=0; i < nLockTables; i++) {
      lockTables[i]=new HashMap();
      this.hook771(envImpl,i);
    }
    this.envImpl=envImpl;
    memoryBudget=envImpl.getMemoryBudget();
    this.hook774();
    envConfigUpdate(configMgr);
    envImpl.addConfigObserver(this);
  }
  /** 
 * Process notifications of mutable property changes.
 */
  public void envConfigUpdate(  DbConfigManager configMgr) throws DatabaseException {
    LockInfo.setDeadlockStackTrace(configMgr.getBoolean(EnvironmentParams.TXN_DEADLOCK_STACK_TRACE));
    setLockTableDump(configMgr.getBoolean(EnvironmentParams.TXN_DUMPLOCKS));
  }
  /** 
 * Called when the je.txn.dumpLocks property is changed.
 */
  static void setLockTableDump(  boolean enable){
    lockTableDump=enable;
  }
  protected int getLockTableIndex(  Long nodeId){
    return ((int)nodeId.longValue()) % nLockTables;
  }
  protected int getLockTableIndex(  long nodeId){
    return ((int)nodeId) % nLockTables;
  }
  /** 
 * Attempt to acquire a lock of <i>type</i> on <i>nodeId</i>. If the lock
 * acquisition would result in a deadlock, throw an exception.<br>
 * If the requested lock is not currently available, block until it is or
 * until timeout milliseconds have elapsed.<br>
 * If a lock of <i>type</i> is already held, return EXISTING.<br>
 * If a WRITE lock is held and a READ lock is requested, return PROMOTION.<br>
 * If a lock request is for a lock that is not currently held, return either
 * NEW or DENIED depending on whether the lock is granted or not.<br>
 * @param nodeIdThe NodeId to lock.
 * @param lockerThe Locker to lock this on behalf of.
 * @param typeThe lock type requested.
 * @param timeoutmilliseconds to time out after if lock couldn't be obtained. 0
 * means block indefinitely. Not used if nonBlockingRequest is
 * true.
 * @param nonBlockingRequestif true, means don't block if lock can't be acquired, and
 * ignore the timeout parameter.
 * @return a LockGrantType indicating whether the request was fulfilled or
 * not. LockGrantType.NEW means the lock grant was fulfilled and the
 * caller did not previously hold the lock. PROMOTION means the lock
 * was granted and it was a promotion from READ to WRITE. EXISTING
 * means the lock was already granted (not a promotion). DENIED
 * means the lock was not granted either because the timeout passed
 * without acquiring the lock or timeout was -1 and the lock was not
 * immediately available.
 * @throws DeadlockExceptionif acquiring the lock would result in a deadlock.
 */
  public LockGrantType lock(  long nodeId,  Locker locker,  LockType type,  long timeout,  boolean nonBlockingRequest,  DatabaseImpl database) throws DeadlockException, DatabaseException {
    assert timeout >= 0;
synchronized (locker) {
      Long nid=new Long(nodeId);
      LockAttemptResult result=attemptLock(nid,locker,type,nonBlockingRequest);
      if (result.success || result.lockGrant == LockGrantType.DENIED) {
        return result.lockGrant;
      }
      this.hook772(nonBlockingRequest);
      assert !nonBlockingRequest;
      try {
        boolean doWait=true;
        if (locker.isTimedOut()) {
          if (validateOwnership(nid,locker,type,true,memoryBudget)) {
            doWait=false;
          }
 else {
            String errMsg=makeTimeoutMsg("Transaction",locker,nodeId,type,result.lockGrant,result.useLock,locker.getTxnTimeOut(),locker.getTxnStartMillis(),System.currentTimeMillis(),database);
            throw new DeadlockException(errMsg);
          }
        }
        boolean keepTime=(timeout > 0);
        long startTime=(keepTime ? System.currentTimeMillis() : 0);
        while (doWait) {
          locker.setWaitingFor(result.useLock);
          try {
            locker.wait(timeout);
          }
 catch (          InterruptedException IE) {
            throw new RunRecoveryException(envImpl,IE);
          }
          boolean lockerTimedOut=locker.isTimedOut();
          long now=System.currentTimeMillis();
          boolean thisLockTimedOut=(keepTime && (now - startTime > timeout));
          boolean isRestart=(result.lockGrant == LockGrantType.WAIT_RESTART);
          if (validateOwnership(nid,locker,type,lockerTimedOut || thisLockTimedOut || isRestart,memoryBudget)) {
            break;
          }
 else {
            if (isRestart) {
              throw rangeRestartException;
            }
            if (thisLockTimedOut) {
              locker.setOnlyAbortable();
              String errMsg=makeTimeoutMsg("Lock",locker,nodeId,type,result.lockGrant,result.useLock,timeout,startTime,now,database);
              throw new DeadlockException(errMsg);
            }
            if (lockerTimedOut) {
              locker.setOnlyAbortable();
              String errMsg=makeTimeoutMsg("Transaction",locker,nodeId,type,result.lockGrant,result.useLock,locker.getTxnTimeOut(),locker.getTxnStartMillis(),now,database);
              throw new DeadlockException(errMsg);
            }
          }
        }
      }
  finally {
        locker.setWaitingFor(null);
        assert EnvironmentImpl.maybeForceYield();
      }
      locker.addLock(nid,result.useLock,type,result.lockGrant);
      return result.lockGrant;
    }
  }
  abstract protected LockAttemptResult attemptLock(  Long nodeId,  Locker locker,  LockType type,  boolean nonBlockingRequest) throws DatabaseException ;
  protected LockAttemptResult attemptLockInternal(  Long nodeId,  Locker locker,  LockType type,  boolean nonBlockingRequest,  int lockTableIndex) throws DatabaseException {
    Map lockTable=lockTables[lockTableIndex];
    Lock useLock=(Lock)lockTable.get(nodeId);
    if (useLock == null) {
      useLock=new Lock(nodeId);
      lockTable.put(nodeId,useLock);
      this.hook780(lockTableIndex);
    }
    LockGrantType lockGrant=useLock.lock(type,locker,nonBlockingRequest,memoryBudget,lockTableIndex);
    boolean success=false;
    if ((lockGrant == LockGrantType.NEW) || (lockGrant == LockGrantType.PROMOTION)) {
      locker.addLock(nodeId,useLock,type,lockGrant);
      success=true;
    }
 else     if (lockGrant == LockGrantType.EXISTING) {
      success=true;
    }
 else     if (lockGrant == LockGrantType.DENIED) {
    }
 else {
      this.hook775();
    }
    return new LockAttemptResult(useLock,lockGrant,success);
  }
  /** 
 * Create a informative lock or txn timeout message.
 */
  protected abstract String makeTimeoutMsg(  String lockOrTxn,  Locker locker,  long nodeId,  LockType type,  LockGrantType grantType,  Lock useLock,  long timeout,  long start,  long now,  DatabaseImpl database) throws DatabaseException ;
  /** 
 * Do the real work of creating an lock or txn timeout message.
 */
  protected String makeTimeoutMsgInternal(  String lockOrTxn,  Locker locker,  long nodeId,  LockType type,  LockGrantType grantType,  Lock useLock,  long timeout,  long start,  long now,  DatabaseImpl database){
    if (lockTableDump) {
      System.out.println("++++++++++ begin lock table dump ++++++++++");
      for (int i=0; i < nLockTables; i++) {
        StringBuffer sb=new StringBuffer();
        dumpToStringNoLatch(sb,i);
        System.out.println(sb.toString());
      }
      System.out.println("++++++++++ end lock table dump ++++++++++");
    }
    StringBuffer sb=new StringBuffer();
    sb.append(lockOrTxn);
    sb.append(" expired. Locker ").append(locker);
    sb.append(": waited for lock");
    if (database != null) {
      sb.append(" on database=").append(database.getDebugName());
    }
    sb.append(" node=").append(nodeId);
    sb.append(" type=").append(type);
    sb.append(" grant=").append(grantType);
    sb.append(" timeoutMillis=").append(timeout);
    sb.append(" startTime=").append(start);
    sb.append(" endTime=").append(now);
    sb.append("\nOwners: ").append(useLock.getOwnersClone());
    sb.append("\nWaiters: ").append(useLock.getWaitersListClone()).append("\n");
    StringBuffer deadlockInfo=findDeadlock(useLock,locker);
    if (deadlockInfo != null) {
      sb.append(deadlockInfo);
    }
    return sb.toString();
  }
  /** 
 * Release a lock and possibly notify any waiters that they have been
 * granted the lock.
 * @param nodeIdThe node ID of the lock to release.
 * @return true if the lock is released successfully, false if the lock is
 * not currently being held.
 */
  boolean release(  long nodeId,  Locker locker) throws DatabaseException {
    return release(nodeId,null,locker,true);
  }
  /** 
 * Release a lock and possibly notify any waiters that they have been
 * granted the lock.
 * @param lockThe lock to release
 * @return true if the lock is released successfully, false if the lock is
 * not currently being held.
 */
  boolean release(  Lock lock,  Locker locker) throws DatabaseException {
    return release(-1,lock,locker,false);
  }
  /** 
 * Do the work of releasing a lock and notifying any waiters that they have
 * been granted the lock.
 * @param lockThe lock to release. If null, use nodeId to find lock
 * @param nodeIdThe node ID of the lock to release, if lock is null. May not
 * be valid if lock is not null. MUST be valid if
 * removeFromLocker is true
 * @param locker
 * @param removeFromLockertrue if we're responsible for
 * @return true if the lock is released successfully, false if the lock is
 * not currently being held.
 */
  private boolean release(  long nodeId,  Lock lock,  Locker locker,  boolean removeFromLocker) throws DatabaseException {
synchronized (locker) {
      Set newOwners=releaseAndFindNotifyTargets(nodeId,lock,locker,removeFromLocker);
      if (newOwners == null) {
        return false;
      }
      if (newOwners.size() > 0) {
        Iterator iter=newOwners.iterator();
        while (iter.hasNext()) {
          Locker lockerToNotify=(Locker)iter.next();
synchronized (lockerToNotify) {
            lockerToNotify.notifyAll();
          }
          assert EnvironmentImpl.maybeForceYield();
        }
      }
      return true;
    }
  }
  /** 
 * Release the lock, and return the set of new owners to notify, if any.
 * @return null if the lock does not exist or the given locker was not the
 * owner, a non-empty set if owners should be notified after
 * releasing, an empty set if no notification is required.
 */
  protected abstract Set releaseAndFindNotifyTargets(  long nodeId,  Lock lock,  Locker locker,  boolean removeFromLocker) throws DatabaseException ;
  /** 
 * Do the real work of releaseAndFindNotifyTargets
 */
  protected Set releaseAndFindNotifyTargetsInternal(  long nodeId,  Lock lock,  Locker locker,  boolean removeFromLocker,  int lockTableIndex) throws DatabaseException {
    Lock useLock=lock;
    Map lockTable=lockTables[lockTableIndex];
    if (useLock == null) {
      useLock=(Lock)lockTable.get(new Long(nodeId));
    }
    if (useLock == null) {
      return null;
    }
    Set lockersToNotify=useLock.release(locker,memoryBudget,lockTableIndex);
    if (lockersToNotify == null) {
      return null;
    }
    if (removeFromLocker) {
      assert nodeId != -1;
      locker.removeLock(nodeId,useLock);
    }
    if ((useLock.nWaiters() == 0) && (useLock.nOwners() == 0)) {
      lockTables[lockTableIndex].remove(useLock.getNodeId());
      this.hook781(lockTableIndex);
    }
    return lockersToNotify;
  }
  /** 
 * Transfer ownership a lock from one locker to another locker. We're not
 * sending any notification to the waiters on the lock table, and the past
 * and present owner should be ready for the transfer.
 */
  abstract void transfer(  long nodeId,  Locker owningLocker,  Locker destLocker,  boolean demoteToRead) throws DatabaseException ;
  /** 
 * Do the real work of transfer
 */
  protected void transferInternal(  long nodeId,  Locker owningLocker,  Locker destLocker,  boolean demoteToRead,  int lockTableIndex) throws DatabaseException {
    Map lockTable=lockTables[lockTableIndex];
    Lock useLock=(Lock)lockTable.get(new Long(nodeId));
    assert useLock != null : "Transfer, lock " + nodeId + " was null";
    if (demoteToRead) {
      useLock.demote(owningLocker);
    }
    useLock.transfer(owningLocker,destLocker,memoryBudget,lockTableIndex);
    owningLocker.removeLock(nodeId,useLock);
  }
  /** 
 * Transfer ownership a lock from one locker to a set of other txns, cloning
 * the lock as necessary. This will always be demoted to read, as we can't
 * have multiple locker owners any other way. We're not sending any
 * notification to the waiters on the lock table, and the past and present
 * owners should be ready for the transfer.
 */
  abstract void transferMultiple(  long nodeId,  Locker owningLocker,  Locker[] destLockers) throws DatabaseException ;
  /** 
 * Do the real work of transferMultiple
 */
  protected void transferMultipleInternal(  long nodeId,  Locker owningLocker,  Locker[] destLockers,  int lockTableIndex) throws DatabaseException {
    Map lockTable=lockTables[lockTableIndex];
    Lock useLock=(Lock)lockTable.get(new Long(nodeId));
    assert useLock != null : "Transfer, lock " + nodeId + " was null";
    useLock.demote(owningLocker);
    useLock.transferMultiple(owningLocker,destLockers,memoryBudget,lockTableIndex);
    owningLocker.removeLock(nodeId,useLock);
  }
  /** 
 * Demote a lock from write to read. Call back to the owning locker to move
 * this to its read collection.
 * @param lockThe lock to release. If null, use nodeId to find lock
 * @param locker
 */
  abstract void demote(  long nodeId,  Locker locker) throws DatabaseException ;
  /** 
 * Do the real work of demote.
 */
  protected void demoteInternal(  long nodeId,  Locker locker,  int lockTableIndex) throws DatabaseException {
    Map lockTable=lockTables[lockTableIndex];
    Lock useLock=(Lock)lockTable.get(new Long(nodeId));
    useLock.demote(locker);
    locker.moveWriteToReadLock(nodeId,useLock);
  }
  /** 
 * Test the status of the lock on nodeId. If any transaction holds any lock
 * on it, true is returned. If no transaction holds a lock on it, false is
 * returned.
 * This method is only used by unit tests.
 * @param nodeIdThe NodeId to check.
 * @return true if any transaction holds any lock on the nodeid. false if no
 * lock is held by any transaction.
 */
  abstract boolean isLocked(  Long nodeId) throws DatabaseException ;
  /** 
 * Do the real work of isLocked.
 */
  protected boolean isLockedInternal(  Long nodeId,  int lockTableIndex){
    Map lockTable=lockTables[lockTableIndex];
    Lock entry=(Lock)lockTable.get(nodeId);
    if (entry == null) {
      return false;
    }
    return entry.nOwners() != 0;
  }
  /** 
 * Return true if this locker owns this a lock of this type on given node.
 * This method is only used by unit tests.
 */
  abstract boolean isOwner(  Long nodeId,  Locker locker,  LockType type) throws DatabaseException ;
  /** 
 * Do the real work of isOwner.
 */
  protected boolean isOwnerInternal(  Long nodeId,  Locker locker,  LockType type,  int lockTableIndex){
    Map lockTable=lockTables[lockTableIndex];
    Lock entry=(Lock)lockTable.get(nodeId);
    if (entry == null) {
      return false;
    }
    return entry.isOwner(locker,type);
  }
  /** 
 * Return true if this locker is waiting on this lock.
 * This method is only used by unit tests.
 */
  abstract boolean isWaiter(  Long nodeId,  Locker locker) throws DatabaseException ;
  /** 
 * Do the real work of isWaiter.
 */
  protected boolean isWaiterInternal(  Long nodeId,  Locker locker,  int lockTableIndex){
    Map lockTable=lockTables[lockTableIndex];
    Lock entry=(Lock)lockTable.get(nodeId);
    if (entry == null) {
      return false;
    }
    return entry.isWaiter(locker);
  }
  /** 
 * Return the number of waiters for this lock.
 */
  abstract int nWaiters(  Long nodeId) throws DatabaseException ;
  /** 
 * Do the real work of nWaiters.
 */
  protected int nWaitersInternal(  Long nodeId,  int lockTableIndex){
    Map lockTable=lockTables[lockTableIndex];
    Lock entry=(Lock)lockTable.get(nodeId);
    if (entry == null) {
      return -1;
    }
    return entry.nWaiters();
  }
  /** 
 * Return the number of owners of this lock.
 */
  abstract int nOwners(  Long nodeId) throws DatabaseException ;
  /** 
 * Do the real work of nWaiters.
 */
  protected int nOwnersInternal(  Long nodeId,  int lockTableIndex){
    Map lockTable=lockTables[lockTableIndex];
    Lock entry=(Lock)lockTable.get(nodeId);
    if (entry == null) {
      return -1;
    }
    return entry.nOwners();
  }
  /** 
 * @return the transaction that owns the write lock for this
 */
  abstract Locker getWriteOwnerLocker(  Long nodeId) throws DatabaseException ;
  /** 
 * Do the real work of getWriteOwnerLocker.
 */
  protected Locker getWriteOwnerLockerInternal(  Long nodeId,  int lockTableIndex) throws DatabaseException {
    Map lockTable=lockTables[lockTableIndex];
    Lock lock=(Lock)lockTable.get(nodeId);
    if (lock == null) {
      return null;
    }
 else     if (lock.nOwners() > 1) {
      return null;
    }
 else {
      return lock.getWriteOwnerLocker();
    }
  }
  abstract protected boolean validateOwnership(  Long nodeId,  Locker locker,  LockType type,  boolean flushFromWaiters,  MemoryBudget mb) throws DatabaseException ;
  protected boolean validateOwnershipInternal(  Long nodeId,  Locker locker,  LockType type,  boolean flushFromWaiters,  MemoryBudget mb,  int lockTableIndex) throws DatabaseException {
    if (isOwnerInternal(nodeId,locker,type,lockTableIndex)) {
      return true;
    }
    if (flushFromWaiters) {
      Lock entry=(Lock)lockTables[lockTableIndex].get(nodeId);
      if (entry != null) {
        entry.flushWaiter(locker,mb,lockTableIndex);
      }
    }
    return false;
  }
  /** 
 * Dump the lock table to the lock stats.
 */
  abstract protected void dumpLockTable(  LockStats stats) throws DatabaseException ;
  /** 
 * Do the real work of dumpLockTableInternal.
 */
  protected void dumpLockTableInternal(  LockStats stats,  int i){
    Map lockTable=lockTables[i];
    this.hook776(stats,lockTable);
    Iterator iter=lockTable.values().iterator();
    while (iter.hasNext()) {
      Lock lock=(Lock)iter.next();
      this.hook777(stats,lock);
      Iterator ownerIter=lock.getOwnersClone().iterator();
      while (ownerIter.hasNext()) {
        LockInfo info=(LockInfo)ownerIter.next();
        this.hook778(stats,info);
      }
    }
  }
  /** 
 * Debugging
 */
  public void dump() throws DatabaseException {
    System.out.println(dumpToString());
  }
  public String dumpToString() throws DatabaseException {
    StringBuffer sb=new StringBuffer();
    for (int i=0; i < nLockTables; i++) {
      this.hook773(sb,i);
    }
    return sb.toString();
  }
  private void dumpToStringNoLatch(  StringBuffer sb,  int whichTable){
    Map lockTable=lockTables[whichTable];
    Iterator entries=lockTable.entrySet().iterator();
    while (entries.hasNext()) {
      Map.Entry entry=(Map.Entry)entries.next();
      Long nid=(Long)entry.getKey();
      Lock lock=(Lock)entry.getValue();
      sb.append("---- Node Id: ").append(nid).append("----\n");
      sb.append(lock);
      sb.append('\n');
    }
  }
  private StringBuffer findDeadlock(  Lock lock,  Locker rootLocker){
    Set ownerSet=new HashSet();
    ownerSet.add(rootLocker);
    StringBuffer ret=findDeadlock1(ownerSet,lock,rootLocker);
    if (ret != null) {
      return ret;
    }
 else {
      return null;
    }
  }
  private StringBuffer findDeadlock1(  Set ownerSet,  Lock lock,  Locker rootLocker){
    Iterator ownerIter=lock.getOwnersClone().iterator();
    while (ownerIter.hasNext()) {
      LockInfo info=(LockInfo)ownerIter.next();
      Locker locker=info.getLocker();
      Lock waitsFor=locker.getWaitingFor();
      if (ownerSet.contains(locker) || locker == rootLocker) {
        StringBuffer ret=new StringBuffer();
        ret.append("Transaction ").append(locker.toString());
        ret.append(" owns ").append(lock.getNodeId());
        ret.append(" ").append(info).append("\n");
        ret.append("Transaction ").append(locker.toString());
        ret.append(" waits for ");
        if (waitsFor == null) {
          ret.append(" nothing");
        }
 else {
          ret.append(" node ");
          ret.append(waitsFor.getNodeId());
        }
        ret.append("\n");
        return ret;
      }
      if (waitsFor != null) {
        ownerSet.add(locker);
        StringBuffer sb=findDeadlock1(ownerSet,waitsFor,rootLocker);
        if (sb != null) {
          String waitInfo="Transaction " + locker + " waits for node "+ waitsFor.getNodeId()+ "\n";
          sb.insert(0,waitInfo);
          return sb;
        }
        ownerSet.remove(locker);
      }
    }
    return null;
  }
  /** 
 * This is just a struct to hold a multi-value return.
 */
static class LockAttemptResult {
    boolean success;
    Lock useLock;
    LockGrantType lockGrant;
    LockAttemptResult(    Lock useLock,    LockGrantType lockGrant,    boolean success){
      this.useLock=useLock;
      this.lockGrant=lockGrant;
      this.success=success;
    }
  }
  protected void hook770() throws DatabaseException {
  }
  protected void hook771(  EnvironmentImpl envImpl,  int i) throws DatabaseException {
  }
  protected void hook772(  boolean nonBlockingRequest) throws DeadlockException, DatabaseException {
  }
  protected void hook773(  StringBuffer sb,  int i) throws DatabaseException {
    dumpToStringNoLatch(sb,i);
  }
  protected void hook774() throws DatabaseException {
  }
  protected void hook775() throws DatabaseException {
  }
  protected void hook776(  LockStats stats,  Map lockTable){
  }
  protected void hook777(  LockStats stats,  Lock lock){
  }
  protected void hook778(  LockStats stats,  LockInfo info){
  }
  protected void hook779(  DbConfigManager configMgr) throws DatabaseException {
  }
  protected void hook780(  int lockTableIndex) throws DatabaseException {
  }
  protected void hook781(  int lockTableIndex) throws DatabaseException {
  }
}
