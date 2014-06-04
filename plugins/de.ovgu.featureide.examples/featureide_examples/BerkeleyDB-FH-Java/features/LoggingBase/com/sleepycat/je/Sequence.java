package com.sleepycat.je;
public class Sequence {
  private Logger logger;
  protected void hook84(  Database db) throws DatabaseException {
    logger=db.getEnvironment().getEnvironmentImpl().getLogger();
    original(db);
  }
}
