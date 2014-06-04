package com.sleepycat.je.tree;
public class BIN {
  protected void hook609(  BINReference binRef,  DatabaseImpl db) throws DatabaseException {
    db.getDbEnvironment().addToCompressorQueue(binRef,false);
    original(binRef,db);
  }
}
