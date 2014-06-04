package com.sleepycat.je.txn;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;
import com.sleepycat.je.Database;
import com.sleepycat.je.DatabaseException;
import com.sleepycat.je.LockStats;
import com.sleepycat.je.dbi.CursorImpl;
import com.sleepycat.je.dbi.DatabaseImpl;
import com.sleepycat.je.dbi.EnvironmentImpl;
import com.sleepycat.je.utilint.DbLsn;
import de.ovgu.cide.jakutil.*;
/** 
 * A concrete Locker that simply tracks locks and releases them when
 * operationEnd is called.
 */
public class BasicLocker extends Locker {
  private Lock ownedLock;
  private Set ownedLockSet;
  /** 
 * Creates a BasicLocker.
 */
  public BasicLocker(  EnvironmentImpl env) throws DatabaseException {
    super(env,false,false);
  }
  /** 
 * BasicLockers always have a fixed id, because they are never used for
 * recovery.
 */
  protected long generateId(  TxnManager txnManager){
    return TxnManager.NULL_TXN_ID;
  }
  protected void checkState(  boolean ignoreCalledByAbort) throws DatabaseException {
  }
  /** 
 * @see Locker#lockInternal
 * @Override
 */
  LockResult lockInternal(  long nodeId,  LockType lockType,  boolean noWait,  DatabaseImpl database) throws DatabaseException {
synchronized (this) {
      checkState(false);
    }
    long timeout=0;
    boolean useNoWait=noWait || defaultNoWait;
    if (!useNoWait) {
synchronized (this) {
        timeout=lockTimeOutMillis;
      }
    }
    LockGrantType grant=lockManager.lock(nodeId,this,lockType,timeout,useNoWait,database);
    return new LockResult(grant,null);
  }
  /** 
 * Get the txn that owns the lock on this node. Return null if there's no
 * owning txn found.
 */
  public Locker getWriteOwnerLocker(  long nodeId) throws DatabaseException {
    return lockManager.getWriteOwnerLocker(new Long(nodeId));
  }
  /** 
 * Get the abort LSN for this node in the txn that owns the lock on this
 * node. Return null if there's no owning txn found.
 */
  public long getOwnerAbortLsn(  long nodeId) throws DatabaseException {
    Locker ownerTxn=lockManager.getWriteOwnerLocker(new Long(nodeId));
    if (ownerTxn != null) {
      return ownerTxn.getAbortLsn(nodeId);
    }
    return DbLsn.NULL_LSN;
  }
  /** 
 * Is never transactional.
 */
  public boolean isTransactional(){
    return false;
  }
  /** 
 * Is never serializable isolation.
 */
  public boolean isSerializableIsolation(){
    return false;
  }
  /** 
 * Is never read-committed isolation.
 */
  public boolean isReadCommittedIsolation(){
    return false;
  }
  /** 
 * No transactional locker is available.
 */
  public Txn getTxnLocker(){
    return null;
  }
  /** 
 * Creates a new instance of this txn for the same environment.  No
 * transactional locks are held by this object, so no locks are retained.
 */
  public Locker newNonTxnLocker() throws DatabaseException {
    return new BasicLocker(envImpl);
  }
  /** 
 * Releases all locks, since all locks held by this locker are
 * non-transactional.
 */
  public void releaseNonTxnLocks() throws DatabaseException {
    operationEnd(true);
  }
  /** 
 * Release locks at the end of the transaction.
 */
  public void operationEnd() throws DatabaseException {
    operationEnd(true);
  }
  /** 
 * Release locks at the end of the transaction.
 */
  public void operationEnd(  boolean operationOK) throws DatabaseException {
    if (ownedLock != null) {
      lockManager.release(ownedLock,this);
      ownedLock=null;
    }
    if (ownedLockSet != null) {
      Iterator iter=ownedLockSet.iterator();
      while (iter.hasNext()) {
        Lock l=(Lock)iter.next();
        lockManager.release(l,this);
      }
      ownedLockSet.clear();
    }
  }
  /** 
 * Transfer any MapLN locks to the db handle.
 */
  public void setHandleLockOwner(  boolean ignore,  Database dbHandle,  boolean dbIsClosing) throws DatabaseException {
    if (dbHandle != null) {
      if (!dbIsClosing) {
        transferHandleLockToHandle(dbHandle);
      }
      unregisterHandle(dbHandle);
    }
  }
  /** 
 * This txn doesn't store cursors.
 */
  public void registerCursor(  CursorImpl cursor) throws DatabaseException {
  }
  /** 
 * This txn doesn't store cursors.
 */
  public void unRegisterCursor(  CursorImpl cursor) throws DatabaseException {
  }
  /** 
 * @return the abort LSN for this node.
 */
  public long getAbortLsn(  long nodeId) throws DatabaseException {
    return DbLsn.NULL_LSN;
  }
  /** 
 * @return a dummy WriteLockInfo for this node.
 */
  public WriteLockInfo getWriteLockInfo(  long nodeId) throws DatabaseException {
    return WriteLockInfo.basicWriteLockInfo;
  }
  /** 
 * Add a lock to set owned by this transaction. 
 */
  void addLock(  Long nodeId,  Lock lock,  LockType type,  LockGrantType grantStatus) throws DatabaseException {
    if (ownedLock == lock || (ownedLockSet != null && ownedLockSet.contains(lock))) {
      return;
    }
    if (ownedLock == null) {
      ownedLock=lock;
    }
 else {
      if (ownedLockSet == null) {
        ownedLockSet=new HashSet();
      }
      ownedLockSet.add(lock);
    }
  }
  /** 
 * Remove a lock from the set owned by this txn.
 */
  void removeLock(  long nodeId,  Lock lock) throws DatabaseException {
    if (lock == ownedLock) {
      ownedLock=null;
    }
 else     if (ownedLockSet != null) {
      ownedLockSet.remove(lock);
    }
  }
  /** 
 * Always false for this txn.
 */
  public boolean createdNode(  long nodeId) throws DatabaseException {
    return false;
  }
  /** 
 * A lock is being demoted. Move it from the write collection into the read
 * collection.
 */
  void moveWriteToReadLock(  long nodeId,  Lock lock){
  }
}
