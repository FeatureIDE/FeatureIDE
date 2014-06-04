package com.sleepycat.je.txn;
import java.util.Set;
import com.sleepycat.je.DatabaseException;
import com.sleepycat.je.LockStats;
import com.sleepycat.je.dbi.DatabaseImpl;
import com.sleepycat.je.dbi.EnvironmentImpl;
import com.sleepycat.je.dbi.MemoryBudget;
import de.ovgu.cide.jakutil.*;
/** 
 * SyncedLockManager uses the synchronized keyword to implement its critical
 * sections.
 */
public class SyncedLockManager extends LockManager {
  public SyncedLockManager(  EnvironmentImpl envImpl) throws DatabaseException {
    super(envImpl);
  }
  /** 
 * @see LockManager#attemptLock
 */
  protected LockAttemptResult attemptLock(  Long nodeId,  Locker locker,  LockType type,  boolean nonBlockingRequest) throws DatabaseException {
    try {
      int lockTableIndex=getLockTableIndex(nodeId);
      this.hook782(nodeId,locker,type,nonBlockingRequest,lockTableIndex);
      throw ReturnHack.returnObject;
    }
 catch (    ReturnObject r) {
      return (LockAttemptResult)r.value;
    }
  }
  /** 
 * @see LockManager#makeTimeoutMsg
 */
  protected String makeTimeoutMsg(  String lockOrTxn,  Locker locker,  long nodeId,  LockType type,  LockGrantType grantType,  Lock useLock,  long timeout,  long start,  long now,  DatabaseImpl database){
    try {
      int lockTableIndex=getLockTableIndex(nodeId);
      this.hook783(lockOrTxn,locker,nodeId,type,grantType,useLock,timeout,start,now,database,lockTableIndex);
      throw ReturnHack.returnObject;
    }
 catch (    ReturnObject r) {
      return (String)r.value;
    }
  }
  /** 
 * @see LockManager#releaseAndNotifyTargets
 */
  protected Set releaseAndFindNotifyTargets(  long nodeId,  Lock lock,  Locker locker,  boolean removeFromLocker) throws DatabaseException {
    try {
      long nid=nodeId;
      if (nid == -1) {
        nid=lock.getNodeId().longValue();
      }
      int lockTableIndex=getLockTableIndex(nid);
      this.hook784(nodeId,lock,locker,removeFromLocker,lockTableIndex);
      throw ReturnHack.returnObject;
    }
 catch (    ReturnObject r) {
      return (Set)r.value;
    }
  }
  /** 
 * @see LockManager#transfer
 */
  void transfer(  long nodeId,  Locker owningLocker,  Locker destLocker,  boolean demoteToRead) throws DatabaseException {
    int lockTableIndex=getLockTableIndex(nodeId);
    this.hook785(nodeId,owningLocker,destLocker,demoteToRead,lockTableIndex);
  }
  /** 
 * @see LockManager#transferMultiple
 */
  void transferMultiple(  long nodeId,  Locker owningLocker,  Locker[] destLockers) throws DatabaseException {
    int lockTableIndex=getLockTableIndex(nodeId);
    this.hook786(nodeId,owningLocker,destLockers,lockTableIndex);
  }
  /** 
 * @see LockManager#demote
 */
  void demote(  long nodeId,  Locker locker) throws DatabaseException {
    int lockTableIndex=getLockTableIndex(nodeId);
    this.hook787(nodeId,locker,lockTableIndex);
  }
  /** 
 * @see LockManager#isLocked
 */
  boolean isLocked(  Long nodeId){
    try {
      int lockTableIndex=getLockTableIndex(nodeId);
      this.hook788(nodeId,lockTableIndex);
      throw ReturnHack.returnBoolean;
    }
 catch (    ReturnBoolean r) {
      return r.value;
    }
  }
  /** 
 * @see LockManager#isOwner
 */
  boolean isOwner(  Long nodeId,  Locker locker,  LockType type){
    try {
      int lockTableIndex=getLockTableIndex(nodeId);
      this.hook789(nodeId,locker,type,lockTableIndex);
      throw ReturnHack.returnBoolean;
    }
 catch (    ReturnBoolean r) {
      return r.value;
    }
  }
  /** 
 * @see LockManager#isWaiter
 */
  boolean isWaiter(  Long nodeId,  Locker locker){
    try {
      int lockTableIndex=getLockTableIndex(nodeId);
      this.hook790(nodeId,locker,lockTableIndex);
      throw ReturnHack.returnBoolean;
    }
 catch (    ReturnBoolean r) {
      return r.value;
    }
  }
  /** 
 * @see LockManager#nWaiters
 */
  int nWaiters(  Long nodeId){
    try {
      int lockTableIndex=getLockTableIndex(nodeId);
      this.hook791(nodeId,lockTableIndex);
      throw ReturnHack.returnInt;
    }
 catch (    ReturnInt r) {
      return r.value;
    }
  }
  /** 
 * @see LockManager#nOwners
 */
  int nOwners(  Long nodeId){
    try {
      int lockTableIndex=getLockTableIndex(nodeId);
      this.hook792(nodeId,lockTableIndex);
      throw ReturnHack.returnInt;
    }
 catch (    ReturnInt r) {
      return r.value;
    }
  }
  /** 
 * @see LockManager#getWriterOwnerLocker
 */
  Locker getWriteOwnerLocker(  Long nodeId) throws DatabaseException {
    try {
      int lockTableIndex=getLockTableIndex(nodeId);
      this.hook793(nodeId,lockTableIndex);
      throw ReturnHack.returnObject;
    }
 catch (    ReturnObject r) {
      return (Locker)r.value;
    }
  }
  /** 
 * @see LockManager#validateOwnership
 */
  protected boolean validateOwnership(  Long nodeId,  Locker locker,  LockType type,  boolean flushFromWaiters,  MemoryBudget mb) throws DatabaseException {
    try {
      int lockTableIndex=getLockTableIndex(nodeId);
      this.hook794(nodeId,locker,type,flushFromWaiters,mb,lockTableIndex);
      throw ReturnHack.returnBoolean;
    }
 catch (    ReturnBoolean r) {
      return r.value;
    }
  }
  /** 
 * @see LockManager#dumpLockTable
 */
  protected void dumpLockTable(  LockStats stats) throws DatabaseException {
    for (int i=0; i < nLockTables; i++) {
      this.hook795(stats,i);
    }
  }
  protected void hook782(  Long nodeId,  Locker locker,  LockType type,  boolean nonBlockingRequest,  int lockTableIndex) throws DatabaseException {
    throw new ReturnObject(attemptLockInternal(nodeId,locker,type,nonBlockingRequest,lockTableIndex));
  }
  protected void hook783(  String lockOrTxn,  Locker locker,  long nodeId,  LockType type,  LockGrantType grantType,  Lock useLock,  long timeout,  long start,  long now,  DatabaseImpl database,  int lockTableIndex){
    throw new ReturnObject(makeTimeoutMsgInternal(lockOrTxn,locker,nodeId,type,grantType,useLock,timeout,start,now,database));
  }
  protected void hook784(  long nodeId,  Lock lock,  Locker locker,  boolean removeFromLocker,  int lockTableIndex) throws DatabaseException {
    throw new ReturnObject(releaseAndFindNotifyTargetsInternal(nodeId,lock,locker,removeFromLocker,lockTableIndex));
  }
  protected void hook785(  long nodeId,  Locker owningLocker,  Locker destLocker,  boolean demoteToRead,  int lockTableIndex) throws DatabaseException {
    transferInternal(nodeId,owningLocker,destLocker,demoteToRead,lockTableIndex);
  }
  protected void hook786(  long nodeId,  Locker owningLocker,  Locker[] destLockers,  int lockTableIndex) throws DatabaseException {
    transferMultipleInternal(nodeId,owningLocker,destLockers,lockTableIndex);
  }
  protected void hook787(  long nodeId,  Locker locker,  int lockTableIndex) throws DatabaseException {
    demoteInternal(nodeId,locker,lockTableIndex);
  }
  protected void hook788(  Long nodeId,  int lockTableIndex){
    throw new ReturnBoolean(isLockedInternal(nodeId,lockTableIndex));
  }
  protected void hook789(  Long nodeId,  Locker locker,  LockType type,  int lockTableIndex){
    throw new ReturnBoolean(isOwnerInternal(nodeId,locker,type,lockTableIndex));
  }
  protected void hook790(  Long nodeId,  Locker locker,  int lockTableIndex){
    throw new ReturnBoolean(isWaiterInternal(nodeId,locker,lockTableIndex));
  }
  protected void hook791(  Long nodeId,  int lockTableIndex){
    throw new ReturnInt(nWaitersInternal(nodeId,lockTableIndex));
  }
  protected void hook792(  Long nodeId,  int lockTableIndex){
    throw new ReturnInt(nOwnersInternal(nodeId,lockTableIndex));
  }
  protected void hook793(  Long nodeId,  int lockTableIndex) throws DatabaseException {
    throw new ReturnObject(getWriteOwnerLockerInternal(nodeId,lockTableIndex));
  }
  protected void hook794(  Long nodeId,  Locker locker,  LockType type,  boolean flushFromWaiters,  MemoryBudget mb,  int lockTableIndex) throws DatabaseException {
    throw new ReturnBoolean(validateOwnershipInternal(nodeId,locker,type,flushFromWaiters,mb,lockTableIndex));
  }
  protected void hook795(  LockStats stats,  int i) throws DatabaseException {
    dumpLockTableInternal(stats,i);
  }
}
