package com.sleepycat.je.txn;
public class Txn {
  private Set deletedDatabases;
  /** 
 * @param dbImpl databaseImpl to remove
 * @param deleteAtCommit true if this databaseImpl should be cleaned on 
 * commit, false if it should be cleaned on abort.
 * @param mb environment memory budget.
 */
  public void markDeleteAtTxnEnd(  DatabaseImpl dbImpl,  boolean deleteAtCommit) throws DatabaseException {
    new Txn_markDeleteAtTxnEnd(this,dbImpl,deleteAtCommit).execute();
  }
  private void setDeletedDatabaseState(  boolean isCommit) throws DatabaseException {
    if (deletedDatabases != null) {
      Iterator iter=deletedDatabases.iterator();
      while (iter.hasNext()) {
        DatabaseCleanupInfo info=(DatabaseCleanupInfo)iter.next();
        if (info.deleteAtCommit == isCommit) {
          info.dbImpl.startDeleteProcessing();
        }
      }
    }
  }
  /** 
 * Cleanup leftover databaseImpls that are a by-product of database
 * operations like removeDatabase(), truncateDatabase().
 * This method must be called outside the synchronization on this txn,
 * because it calls deleteAndReleaseINs, which gets the TxnManager's
 * allTxns latch. The checkpointer also gets the allTxns latch, and within
 * that latch, needs to synchronize on individual txns, so we must avoid a
 * latching hiearchy conflict.
 */
  private void cleanupDatabaseImpls(  boolean isCommit) throws DatabaseException {
    if (deletedDatabases != null) {
      DatabaseCleanupInfo[] infoArray;
synchronized (this) {
        infoArray=new DatabaseCleanupInfo[deletedDatabases.size()];
        deletedDatabases.toArray(infoArray);
      }
      for (int i=0; i < infoArray.length; i+=1) {
        DatabaseCleanupInfo info=infoArray[i];
        if (info.deleteAtCommit == isCommit) {
          info.dbImpl.releaseDeletedINs();
        }
      }
      deletedDatabases=null;
    }
  }
  protected void hook805() throws DatabaseException, RunRecoveryException, Throwable {
    cleanupDatabaseImpls(true);
    original();
  }
  protected void hook806() throws DatabaseException, RunRecoveryException, Throwable {
    setDeletedDatabaseState(true);
    original();
  }
  protected void hook807() throws DatabaseException {
    cleanupDatabaseImpls(false);
    original();
  }
  protected void hook808() throws DatabaseException {
    setDeletedDatabaseState(false);
    original();
  }
@MethodObject static class Txn_markDeleteAtTxnEnd {
    Txn_markDeleteAtTxnEnd(    Txn _this,    DatabaseImpl dbImpl,    boolean deleteAtCommit){
      this._this=_this;
      this.dbImpl=dbImpl;
      this.deleteAtCommit=deleteAtCommit;
    }
    void execute() throws DatabaseException {
synchronized (_this) {
        this.hook797();
        if (_this.deletedDatabases == null) {
          _this.deletedDatabases=new HashSet();
          this.hook798();
        }
        _this.deletedDatabases.add(new DatabaseCleanupInfo(dbImpl,deleteAtCommit));
        this.hook796();
      }
    }
    protected Txn _this;
    protected DatabaseImpl dbImpl;
    protected boolean deleteAtCommit;
    protected int delta;
    protected void hook796() throws DatabaseException {
    }
    protected void hook797() throws DatabaseException {
    }
    protected void hook798() throws DatabaseException {
    }
  }
}
