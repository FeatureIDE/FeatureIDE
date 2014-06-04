package com.sleepycat.je;
import com.sleepycat.je.txn.Locker;
import de.ovgu.cide.jakutil.*;
class ForeignKeyTrigger implements DatabaseTrigger {
  private SecondaryDatabase secDb;
  ForeignKeyTrigger(  SecondaryDatabase secDb){
    this.secDb=secDb;
  }
  public void triggerAdded(  Database db){
  }
  public void triggerRemoved(  Database db){
    secDb.clearForeignKeyTrigger();
  }
  public void databaseUpdated(  Database db,  Locker locker,  DatabaseEntry priKey,  DatabaseEntry oldData,  DatabaseEntry newData) throws DatabaseException {
    if (newData == null) {
      secDb.onForeignKeyDelete(locker,priKey);
    }
  }
}
