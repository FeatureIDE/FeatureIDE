package com.sleepycat.je.dbi;
public class EnvironmentImpl {
  /** 
 * Remove a database.
 */
  public void dbRemove(  Locker locker,  String databaseName) throws DatabaseException {
    dbMapTree.dbRemove(locker,databaseName);
  }
}
