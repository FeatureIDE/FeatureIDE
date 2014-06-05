package com.sleepycat.je.dbi;
public class DatabaseImpl {
  private static final short NOT_DELETED=1;
  private static final short DELETED_CLEANUP_INLIST_HARVEST=2;
  private static final short DELETED_CLEANUP_LOG_HARVEST=3;
  private static final short DELETED=4;
  private short deleteState;
  public boolean isDeleted(){
    return !(deleteState == NOT_DELETED);
  }
  public boolean isDeleteFinished(){
    return (deleteState == DELETED);
  }
  public void startDeleteProcessing(){
    assert (deleteState == NOT_DELETED);
    deleteState=DELETED_CLEANUP_INLIST_HARVEST;
  }
  void finishedINListHarvest(){
    assert (deleteState == DELETED_CLEANUP_INLIST_HARVEST);
    deleteState=DELETED_CLEANUP_LOG_HARVEST;
  }
  /** 
 * Purge a DatabaseImpl and corresponding MapLN in the db mapping tree.
 * Purging consists of removing all related INs from the db mapping tree and
 * deleting the related MapLN. Used at the a transaction end in these cases: -
 * purge the deleted database after a commit of Environment.removeDatabase -
 * purge the deleted database after a commit of Environment.truncateDatabase -
 * purge the newly created database after an abort of
 * Environment.truncateDatabase
 */
  public void deleteAndReleaseINs() throws DatabaseException {
    startDeleteProcessing();
    releaseDeletedINs();
  }
  public void releaseDeletedINs() throws DatabaseException {
    if (pendingDeletedHook != null) {
      pendingDeletedHook.doHook();
    }
    try {
      long rootLsn=tree.getRootLsn();
      if (rootLsn == DbLsn.NULL_LSN) {
        envImpl.getDbMapTree().deleteMapLN(id);
      }
 else {
        UtilizationTracker snapshot=new UtilizationTracker(envImpl);
        snapshot.countObsoleteNodeInexact(rootLsn,LogEntryType.LOG_IN);
        ObsoleteProcessor obsoleteProcessor=new ObsoleteProcessor(snapshot);
        SortedLSNTreeWalker walker=new SortedLSNTreeWalker(this,true,true,rootLsn,obsoleteProcessor);
        envImpl.getDbMapTree().deleteMapLN(id);
        walker.walk();
        envImpl.getUtilizationProfile().countAndLogSummaries(snapshot.getTrackedFiles());
      }
    }
  finally {
      deleteState=DELETED;
    }
  }
  public void checkIsDeleted(  String operation) throws DatabaseException {
    if (isDeleted()) {
      throw new DatabaseException("Attempt to " + operation + " a deleted database");
    }
  }
  protected void hook288() throws DatabaseException {
    deleteState=NOT_DELETED;
    original();
  }
  protected void hook289() throws DatabaseException {
    deleteState=NOT_DELETED;
    original();
  }
}
