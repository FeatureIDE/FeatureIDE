package com.sleepycat.je.dbi;
public class EnvironmentImpl {
  /** 
 * Truncate a database. Return a new DatabaseImpl object which represents
 * the new truncated database. The old database is marked as deleted.
 * @deprecated This supports Database.truncate(), which is deprecated.
 */
  public TruncateResult truncate(  Locker locker,  DatabaseImpl database) throws DatabaseException {
    return dbMapTree.truncate(locker,database,true);
  }
  /** 
 * Truncate a database.
 */
  public long truncate(  Locker locker,  String databaseName,  boolean returnCount) throws DatabaseException {
    return dbMapTree.truncate(locker,databaseName,returnCount);
  }
}
