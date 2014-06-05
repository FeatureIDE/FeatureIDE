package com.sleepycat.je;
public class Database {
  protected void hook43() throws DatabaseException {
    databaseImpl.checkIsDeleted("truncate");
    original();
  }
}
