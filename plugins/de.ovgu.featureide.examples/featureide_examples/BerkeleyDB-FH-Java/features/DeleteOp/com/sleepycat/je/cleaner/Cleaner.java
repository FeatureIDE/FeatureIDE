package com.sleepycat.je.cleaner;
public class Cleaner {
  /** 
 * Adds the DB ID to the pending DB set if it is being deleted but deletion
 * is not yet complete.
 */
  void addPendingDB(  DatabaseImpl db){
    if (db != null && db.isDeleted() && !db.isDeleteFinished()) {
      DatabaseId id=db.getId();
      if (fileSelector.addPendingDB(id)) {
        this.hook85(id);
      }
    }
  }
  protected void hook85(  DatabaseId id){
  }
  protected boolean hook112(  DatabaseImpl db,  boolean c) throws DatabaseException {
    c=c || db.isDeleted();
    return original(db,c);
  }
  protected void hook113(  DatabaseImpl db) throws DatabaseException {
    addPendingDB(db);
    original(db);
  }
@MethodObject static class Cleaner_processPending {
    void execute() throws DatabaseException {
      original();
      pendingDBs=_this.fileSelector.getPendingDBs();
      if (pendingDBs != null) {
        for (int i=0; i < pendingDBs.length; i+=1) {
          dbId2=pendingDBs[i];
          db2=dbMapTree.getDb(dbId2,_this.lockTimeout);
          if (db2 == null || db2.isDeleteFinished()) {
            _this.fileSelector.removePendingDB(dbId2);
          }
        }
      }
    }
  }
}
