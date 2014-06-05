package com.sleepycat.je;
public class Database {
  protected void hook37() throws DatabaseException {
    databaseImpl.checkIsDeleted("verify");
    original();
  }
}
