package com.sleepycat.je;
import com.sleepycat.je.txn.Locker;
import de.ovgu.cide.jakutil.*;
class SecondaryTrigger implements DatabaseTrigger {
  private SecondaryDatabase secDb;
  SecondaryTrigger(  SecondaryDatabase secDb){
    this.secDb=secDb;
  }
  final SecondaryDatabase getDb(){
    return secDb;
  }
  public void triggerAdded(  Database db){
  }
  public void triggerRemoved(  Database db){
    secDb.clearPrimary();
  }
  public void databaseUpdated(  Database db,  Locker locker,  DatabaseEntry priKey,  DatabaseEntry oldData,  DatabaseEntry newData) throws DatabaseException {
    secDb.updateSecondary(locker,null,priKey,oldData,newData);
  }
}
