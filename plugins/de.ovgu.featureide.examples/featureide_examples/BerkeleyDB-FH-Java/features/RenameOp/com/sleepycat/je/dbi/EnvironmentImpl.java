package com.sleepycat.je.dbi;
public class EnvironmentImpl {
  /** 
 * Rename a database.
 */
  public void dbRename(  Locker locker,  String databaseName,  String newName) throws DatabaseException {
    dbMapTree.dbRename(locker,databaseName,newName);
  }
}
