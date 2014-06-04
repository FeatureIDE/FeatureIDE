package com.sleepycat.je;
public class Database {
  protected void hook38() throws DatabaseException {
    databaseImpl.checkIsDeleted("stat");
    original();
  }
}
