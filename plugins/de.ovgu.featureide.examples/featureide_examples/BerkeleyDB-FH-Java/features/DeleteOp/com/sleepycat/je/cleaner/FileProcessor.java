package com.sleepycat.je.cleaner;
class FileProcessor {
  protected boolean hook159(  DatabaseImpl db,  boolean b) throws DatabaseException {
    b|=db.isDeleted();
    return original(db,b);
  }
  protected void hook160(  DatabaseImpl db) throws DatabaseException {
    cleaner.addPendingDB(db);
    original(db);
  }
@MethodObject static class FileProcessor_processLN {
    protected void hook157() throws DatabaseException {
      b|=db.isDeleted();
      original();
    }
    protected void hook158() throws DatabaseException {
      _this.cleaner.addPendingDB(db);
      original();
    }
  }
@MethodObject static class FileProcessor_processFile {
    protected void hook154() throws DatabaseException, IOException {
      checkPendingDbSet=new HashSet();
      original();
    }
    protected void hook155() throws DatabaseException, IOException {
      for (Iterator i=checkPendingDbSet.iterator(); i.hasNext(); ) {
        dbId=(DatabaseId)i.next();
        db=dbMapTree.getDb(dbId,_this.cleaner.lockTimeout,dbCache);
        _this.cleaner.addPendingDB(db);
      }
      original();
    }
    protected void hook156() throws DatabaseException, IOException {
      dbId1=reader.getDatabaseId();
      if (dbId1 != null) {
        checkPendingDbSet.add(dbId1);
      }
      original();
    }
  }
}
