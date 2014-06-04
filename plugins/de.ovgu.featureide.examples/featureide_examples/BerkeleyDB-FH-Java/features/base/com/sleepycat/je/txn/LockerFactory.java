package com.sleepycat.je.txn;
import com.sleepycat.je.Database;
import com.sleepycat.je.DatabaseException;
import com.sleepycat.je.DbInternal;
import com.sleepycat.je.Environment;
import com.sleepycat.je.Transaction;
import com.sleepycat.je.TransactionConfig;
import com.sleepycat.je.dbi.DatabaseImpl;
import com.sleepycat.je.dbi.EnvironmentImpl;
import de.ovgu.cide.jakutil.*;
/** 
 * Factory of static methods for creating Locker objects.
 */
public class LockerFactory {
  /** 
 * Get a locker for a writable operation, checking whether the db and
 * environment is transactional or not. Must return a non null locker.
 */
  public static Locker getWritableLocker(  Environment env,  Transaction userTxn,  boolean dbIsTransactional) throws DatabaseException {
    return getWritableLocker(env,userTxn,dbIsTransactional,false,null);
  }
  /** 
 * Get a locker for a writable operation, also specifying whether to retain
 * non-transactional locks when a new locker must be created.
 * @param retainNonTxnLocks is true for DbTree operations, so that the
 * handle lock may be transferred out of the locker when the operation is
 * complete.
 */
  public static Locker getWritableLocker(  Environment env,  Transaction userTxn,  boolean dbIsTransactional,  boolean retainNonTxnLocks,  TransactionConfig autoCommitConfig) throws DatabaseException {
    EnvironmentImpl envImpl=DbInternal.envGetEnvironmentImpl(env);
    boolean envIsTransactional=envImpl.isTransactional();
    if (userTxn == null) {
      Transaction xaLocker=env.getThreadTransaction();
      if (xaLocker != null) {
        return DbInternal.getLocker(xaLocker);
      }
    }
    if (dbIsTransactional && userTxn == null) {
      if (autoCommitConfig == null) {
        autoCommitConfig=DbInternal.getDefaultTxnConfig(env);
      }
      return new AutoTxn(envImpl,autoCommitConfig);
    }
 else     if (userTxn == null) {
      if (retainNonTxnLocks) {
        return new BasicLocker(envImpl);
      }
 else {
        return new ThreadLocker(envImpl);
      }
    }
 else {
      if (!envIsTransactional) {
        throw new DatabaseException("A Transaction cannot be used because the" + " environment was opened" + " non-transactionally");
      }
      if (!dbIsTransactional) {
        throw new DatabaseException("A Transaction cannot be used because the" + " database was opened" + " non-transactionally");
      }
      Locker locker=DbInternal.getLocker(userTxn);
      if (locker.isReadCommittedIsolation() && !retainNonTxnLocks) {
        return new ReadCommittedLocker(envImpl,locker);
      }
 else {
        return locker;
      }
    }
  }
  /** 
 * Get a locker for a read or cursor operation.
 * See getWritableLocker for an explanation of retainNonTxnLocks.
 */
  public static Locker getReadableLocker(  Environment env,  Transaction userTxn,  boolean dbIsTransactional,  boolean retainNonTxnLocks,  boolean readCommittedIsolation) throws DatabaseException {
    if (userTxn != null && !dbIsTransactional) {
      throw new DatabaseException("A Transaction cannot be used because the" + " database was opened" + " non-transactionally");
    }
    Locker locker=null;
    if (userTxn != null) {
      locker=DbInternal.getLocker(userTxn);
      if (locker.isReadCommittedIsolation()) {
        readCommittedIsolation=true;
      }
    }
    return getReadableLocker(env,locker,retainNonTxnLocks,readCommittedIsolation);
  }
  /** 
 * Get a locker for this database handle for a read or cursor operation.
 * See getWritableLocker for an explanation of retainNonTxnLocks.
 */
  public static Locker getReadableLocker(  Environment env,  Database dbHandle,  Locker locker,  boolean retainNonTxnLocks,  boolean readCommittedIsolation) throws DatabaseException {
    DatabaseImpl dbImpl=DbInternal.dbGetDatabaseImpl(dbHandle);
    if (!dbImpl.isTransactional() && locker != null && locker.isTransactional()) {
      throw new DatabaseException("A Transaction cannot be used because the" + " database was opened" + " non-transactionally");
    }
    if (locker != null && !locker.isTransactional() && !retainNonTxnLocks) {
      locker=null;
    }
    if (locker != null && locker.isReadCommittedIsolation()) {
      readCommittedIsolation=true;
    }
    return getReadableLocker(env,locker,retainNonTxnLocks,readCommittedIsolation);
  }
  /** 
 * Get a locker for a read or cursor operation.
 * See getWritableLocker for an explanation of retainNonTxnLocks.
 */
  private static Locker getReadableLocker(  Environment env,  Locker locker,  boolean retainNonTxnLocks,  boolean readCommittedIsolation) throws DatabaseException {
    EnvironmentImpl envImpl=DbInternal.envGetEnvironmentImpl(env);
    if (locker == null) {
      Transaction xaTxn=env.getThreadTransaction();
      if (xaTxn != null) {
        return DbInternal.getLocker(xaTxn);
      }
    }
    if (locker == null) {
      if (retainNonTxnLocks) {
        locker=new BasicLocker(envImpl);
      }
 else {
        locker=new ThreadLocker(envImpl);
      }
    }
 else {
      if (readCommittedIsolation && !retainNonTxnLocks) {
        locker=new ReadCommittedLocker(envImpl,locker);
      }
    }
    return locker;
  }
}
