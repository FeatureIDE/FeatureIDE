package com.sleepycat.je;
public class Cursor {
  private Logger logger;
  protected void hook36(  DatabaseImpl dbImpl) throws DatabaseException {
    this.logger=dbImpl.getDbEnvironment().getLogger();
    original(dbImpl);
  }
  /** 
 * Copy constructor.
 */
  Cursor(  Cursor cursor,  boolean samePosition) throws DatabaseException {
    logger=dbImpl.getDbEnvironment().getLogger();
  }
}
