package com.sleepycat.je.tree;
public final class Tree {
  protected void hook754(  BIN bin) throws DatabaseException, NodeNotEmptyException, CursorsExistException {
    if (bin.getNEntries() == 0) {
      database.getDbEnvironment().addToCompressorQueue(bin,null,false);
    }
    original(bin);
  }
}
