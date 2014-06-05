package com.sleepycat.je.txn;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Hashtable;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;
import com.sleepycat.je.Database;
import com.sleepycat.je.DatabaseException;
import com.sleepycat.je.DeadlockException;
import com.sleepycat.je.DbInternal;
import com.sleepycat.je.LockNotGrantedException;
import com.sleepycat.je.LockStats;
import com.sleepycat.je.OperationStatus;
import com.sleepycat.je.dbi.CursorImpl;
import com.sleepycat.je.dbi.DatabaseImpl;
import com.sleepycat.je.dbi.EnvironmentImpl;
import com.sleepycat.je.tree.BIN;
import com.sleepycat.je.tree.BINReference;
import com.sleepycat.je.tree.Key;
import de.ovgu.cide.jakutil.*;
/** 
 * Locker instances are JE's route to locking and transactional support.  This
 * class is the abstract base class for BasicLocker, ThreadLocker, Txn and
 * AutoTxn.  Locker instances are in fact only a transaction shell to get to
 * the lock manager, and don't guarantee transactional semantics. Txn and
 * AutoTxn instances are both truely transactional, but have different ending
 * behaviors.
 */
public abstract class Locker {
  private static final String DEBUG_NAME=Locker.class.getName();
  protected EnvironmentImpl envImpl;
  protected LockManager lockManager;
  protected long id;
  protected boolean readUncommittedDefault;
  protected boolean defaultNoWait;
  protected long lockTimeOutMillis;
  private long txnTimeOutMillis;
  private long txnStartMillis;
  private Lock waitingFor;
  protected Map handleLockToHandleMap;
  protected Map handleToHandleLockMap;
  /** 
 * The thread that created this locker.  Used for debugging, and by the
 * ThreadLocker subclass. Note that thread may be null if the Locker is
 * instantiated by reading the log.
 */
  protected Thread thread;
  /** 
 * Create a locker id. This constructor is called very often, so it should
 * be as streamlined as possible.
 * @param lockManager lock manager for this environment
 * @param readUncommittedDefault if true, this transaction does
 * read-uncommitted by default
 * @param noWait if true, non-blocking lock requests are used.
 */
  public Locker(  EnvironmentImpl envImpl,  boolean readUncommittedDefault,  boolean noWait) throws DatabaseException {
    TxnManager txnManager=envImpl.getTxnManager();
    this.id=generateId(txnManager);
    this.envImpl=envImpl;
    lockManager=txnManager.getLockManager();
    this.readUncommittedDefault=readUncommittedDefault;
    this.waitingFor=null;
    defaultNoWait=noWait;
    lockTimeOutMillis=envImpl.getLockTimeout();
    txnTimeOutMillis=envImpl.getTxnTimeout();
    if (txnTimeOutMillis != 0) {
      txnStartMillis=System.currentTimeMillis();
    }
 else {
      txnStartMillis=0;
    }
    thread=Thread.currentThread();
  }
  /** 
 * For reading from the log.
 */
  Locker(){
  }
  /** 
 * A Locker has to generate its next id. Some subtypes, like BasicLocker,
 * have a single id for all instances because they are never used for
 * recovery. Other subtypes ask the txn manager for an id.
 */
  protected abstract long generateId(  TxnManager txnManager);
  /** 
 * @return the transaction's id.
 */
  public long getId(){
    return id;
  }
  /** 
 * @return the default no-wait (non-blocking) setting.
 */
  public boolean getDefaultNoWait(){
    return defaultNoWait;
  }
  /** 
 * Get the lock timeout period for this transaction, in milliseconds
 */
  public synchronized long getLockTimeout(){
    return lockTimeOutMillis;
  }
  /** 
 * Set the lock timeout period for any locks in this transaction,
 * in milliseconds.
 */
  public synchronized void setLockTimeout(  long timeOutMillis){
    lockTimeOutMillis=timeOutMillis;
  }
  /** 
 * Set the timeout period for this transaction, in milliseconds.
 */
  public synchronized void setTxnTimeout(  long timeOutMillis){
    txnTimeOutMillis=timeOutMillis;
    txnStartMillis=System.currentTimeMillis();
  }
  /** 
 * @return true if transaction was created with read-uncommitted as a
 * default.
 */
  public boolean isReadUncommittedDefault(){
    return readUncommittedDefault;
  }
  Lock getWaitingFor(){
    return waitingFor;
  }
  void setWaitingFor(  Lock lock){
    waitingFor=lock;
  }
  /** 
 * Set the state of a transaction to ONLY_ABORTABLE.
 */
  void setOnlyAbortable(){
  }
  protected abstract void checkState(  boolean ignoreCalledByAbort) throws DatabaseException ;
  /** 
 * Abstract method to a blocking or non-blocking lock of the given type on
 * the given nodeId.  Unlike the lock() method, this method does not throw
 * LockNotGrantedException and can therefore be used by nonBlockingLock to
 * probe for a lock without the overhead of an exception stack trace.
 * @param nodeId is the node to lock.
 * @param lockType is the type of lock to request.
 * @param noWait is true to override the defaultNoWait setting.  If true,
 * or if defaultNoWait is true, throws LockNotGrantedException if the lock
 * cannot be granted without waiting.
 * @param database is the database containing nodeId.
 * @throws DeadlockException if acquiring a blocking lock would result in a
 * deadlock.
 */
  abstract LockResult lockInternal(  long nodeId,  LockType lockType,  boolean noWait,  DatabaseImpl database) throws DeadlockException, DatabaseException ;
  /** 
 * Request a blocking or non-blocking lock of the given type on the given
 * nodeId.
 * @param nodeId is the node to lock.
 * @param lockType is the type of lock to request.
 * @param noWait is true to override the defaultNoWait setting.  If true,
 * or if defaultNoWait is true, throws LockNotGrantedException if the lock
 * cannot be granted without waiting.
 * @param database is the database containing nodeId.
 * @throws LockNotGrantedException if a non-blocking lock was denied.
 * @throws DeadlockException if acquiring a blocking lock would result in a
 * deadlock.
 */
  public LockResult lock(  long nodeId,  LockType lockType,  boolean noWait,  DatabaseImpl database) throws LockNotGrantedException, DeadlockException, DatabaseException {
    LockResult result=lockInternal(nodeId,lockType,noWait,database);
    if (result.getLockGrant() == LockGrantType.DENIED) {
      throw new LockNotGrantedException("Non-blocking lock was denied.");
    }
 else {
      return result;
    }
  }
  /** 
 * Request a non-blocking lock of the given type on the given nodeId.
 * <p>Unlike lock(), this method returns LockGrantType.DENIED if the lock
 * is denied rather than throwing LockNotGrantedException.  This method
 * should therefore not be used as the final lock for a user operation,
 * since in that case LockNotGrantedException should be thrown for a denied
 * lock.  It is normally used only to probe for a lock, and other recourse
 * is taken if the lock is denied.</p>
 * @param nodeId is the node to lock.
 * @param lockType is the type of lock to request.
 * @param database is the database containing nodeId.
 */
  public LockResult nonBlockingLock(  long nodeId,  LockType lockType,  DatabaseImpl database) throws DatabaseException {
    return lockInternal(nodeId,lockType,true,database);
  }
  /** 
 * Release the lock on this LN and remove from the transaction's owning
 * set.
 */
  public void releaseLock(  long nodeId) throws DatabaseException {
    lockManager.release(nodeId,this);
  }
  /** 
 * Revert this lock from a write lock to a read lock.
 */
  public void demoteLock(  long nodeId) throws DatabaseException {
    lockManager.demote(nodeId,this);
  }
  /** 
 * Returns whether this locker is transactional.
 */
  public abstract boolean isTransactional();
  /** 
 * Returns whether the isolation level of this locker is serializable.
 */
  public abstract boolean isSerializableIsolation();
  /** 
 * Returns whether the isolation level of this locker is read-committed.
 */
  public abstract boolean isReadCommittedIsolation();
  /** 
 * Returns the underlying Txn if the locker is transactional, or null if
 * the locker is non-transactional.  For a Txn-based locker, this method
 * returns 'this'.  For a BuddyLocker, this method may returns the buddy.
 */
  public abstract Txn getTxnLocker();
  /** 
 * Creates a fresh non-transactional locker, while retaining any
 * transactional locks held by this locker.  This method is called when the
 * cursor for this locker is cloned.
 * <p>In general, transactional lockers return 'this' when this method is
 * called, while non-transactional lockers return a new instance.</p>
 */
  public abstract Locker newNonTxnLocker() throws DatabaseException ;
  /** 
 * Releases any non-transactional locks held by this locker.  This method
 * is called when the cursor moves to a new position or is closed.
 * <p>In general, transactional lockers do nothing when this method is
 * called, while non-transactional lockers release all locks as if
 * operationEnd were called.</p>
 */
  public abstract void releaseNonTxnLocks() throws DatabaseException ;
  /** 
 * Returns whether this locker can share locks with the given locker.
 * <p>All lockers share locks with a BuddyLocker whose buddy is this
 * locker.  To support BuddyLocker when overriding this method, always
 * return true if this implementation (super.sharesLocksWith(...)) returns
 * true.</p>
 */
  public boolean sharesLocksWith(  Locker other){
    if (other instanceof BuddyLocker) {
      BuddyLocker buddy=(BuddyLocker)other;
      return buddy.getBuddy() == this;
    }
 else {
      return false;
    }
  }
  /** 
 * The equivalent of calling operationEnd(true).
 */
  public abstract void operationEnd() throws DatabaseException ;
  /** 
 * Different types of transactions do different things when the operation
 * ends. Txns do nothing, AutoTxns commit or abort, and BasicLockers and
 * ThreadLockers just release locks.
 * @param operationOK is whether the operation succeeded, since
 * that may impact ending behavior. (i.e for AutoTxn)
 */
  public abstract void operationEnd(  boolean operationOK) throws DatabaseException ;
  /** 
 * We're at the end of an operation. Move this handle lock to the
 * appropriate owner.
 */
  public abstract void setHandleLockOwner(  boolean operationOK,  Database dbHandle,  boolean dbIsClosing) throws DatabaseException ;
  /** 
 * A SUCCESS status equals operationOk.
 */
  public void operationEnd(  OperationStatus status) throws DatabaseException {
    operationEnd(status == OperationStatus.SUCCESS);
  }
  /** 
 * Tell this transaction about a cursor.
 */
  public abstract void registerCursor(  CursorImpl cursor) throws DatabaseException ;
  /** 
 * Remove a cursor from this txn.
 */
  public abstract void unRegisterCursor(  CursorImpl cursor) throws DatabaseException ;
  /** 
 * @return the abort LSN for this node.
 */
  public abstract long getAbortLsn(  long nodeId) throws DatabaseException ;
  /** 
 * @return the WriteLockInfo for this node.
 */
  public abstract WriteLockInfo getWriteLockInfo(  long nodeId) throws DatabaseException ;
  /** 
 * Add a lock to set owned by this transaction.
 */
  abstract void addLock(  Long nodeId,  Lock lock,  LockType type,  LockGrantType grantStatus) throws DatabaseException ;
  /** 
 * @return true if this transaction created this node,
 * for a operation with transactional semantics.
 */
  public abstract boolean createdNode(  long nodeId) throws DatabaseException ;
  /** 
 * Remove the lock from the set owned by this transaction. If specified to
 * LockManager.release, the lock manager will call this when its releasing
 * a lock.
 */
  abstract void removeLock(  long nodeId,  Lock lock) throws DatabaseException ;
  /** 
 * A lock is being demoted. Move it from the write collection into the read
 * collection.
 */
  abstract void moveWriteToReadLock(  long nodeId,  Lock lock);
  boolean isTimedOut() throws DatabaseException {
    if (txnStartMillis != 0) {
      long diff=System.currentTimeMillis() - txnStartMillis;
      if (diff > txnTimeOutMillis) {
        return true;
      }
    }
    return false;
  }
  public long getTxnTimeOut(){
    return txnTimeOutMillis;
  }
  long getTxnStartMillis(){
    return txnStartMillis;
  }
  /** 
 * Remove this Database from the protected Database handle set
 */
  void unregisterHandle(  Database dbHandle){
    if (handleToHandleLockMap != null) {
      handleToHandleLockMap.remove(dbHandle);
    }
  }
  /** 
 * Remember how handle locks and handles match up.
 */
  public void addToHandleMaps(  Long handleLockId,  Database databaseHandle){
    Set dbHandleSet=null;
    if (handleLockToHandleMap == null) {
      handleLockToHandleMap=new Hashtable();
      handleToHandleLockMap=new Hashtable();
    }
 else {
      dbHandleSet=(Set)handleLockToHandleMap.get(handleLockId);
    }
    if (dbHandleSet == null) {
      dbHandleSet=new HashSet();
      handleLockToHandleMap.put(handleLockId,dbHandleSet);
    }
    dbHandleSet.add(databaseHandle);
    handleToHandleLockMap.put(databaseHandle,handleLockId);
  }
  /** 
 * @return true if this txn is willing to give up the handle lock to
 * another txn before this txn ends.
 */
  public boolean isHandleLockTransferrable(){
    return true;
  }
  /** 
 * The currentTxn passes responsiblity for this db handle lock to a txn
 * owned by the Database object.
 */
  void transferHandleLockToHandle(  Database dbHandle) throws DatabaseException {
    Locker holderTxn=new BasicLocker(envImpl);
    transferHandleLock(dbHandle,holderTxn,true);
  }
  /** 
 */
  public void transferHandleLock(  Database dbHandle,  Locker destLocker,  boolean demoteToRead) throws DatabaseException {
    if (DbInternal.dbGetDatabaseImpl(dbHandle) != null) {
      Long handleLockId=(Long)handleToHandleLockMap.get(dbHandle);
      if (handleLockId != null) {
        long nodeId=handleLockId.longValue();
        lockManager.transfer(nodeId,this,destLocker,demoteToRead);
        destLocker.addToHandleMaps(handleLockId,dbHandle);
        Set dbHandleSet=(Set)handleLockToHandleMap.get(handleLockId);
        Iterator iter=dbHandleSet.iterator();
        while (iter.hasNext()) {
          if (((Database)iter.next()) == dbHandle) {
            iter.remove();
            break;
          }
        }
        if (dbHandleSet.size() == 0) {
          handleLockToHandleMap.remove(handleLockId);
        }
        DbInternal.dbSetHandleLocker(dbHandle,destLocker);
      }
    }
  }
  /** 
 * If necessary, remember that this txn once owned a handle lock.  Done to
 * make commit optimizations work correctly.
 */
  protected void rememberHandleWriteLock(  Long lockId){
  }
  public String toString(){
    String className=getClass().getName();
    className=className.substring(className.lastIndexOf('.') + 1);
    return Long.toString(id) + "_" + ((thread == null) ? "" : thread.getName())+ "_"+ className;
  }
  /** 
 * Dump lock table, for debugging
 */
  public void dumpLockTable() throws DatabaseException {
    lockManager.dump();
  }
}
