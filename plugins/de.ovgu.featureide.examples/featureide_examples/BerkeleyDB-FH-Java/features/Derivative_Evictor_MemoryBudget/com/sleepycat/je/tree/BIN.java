package com.sleepycat.je.tree;
public class BIN {
  protected void hook601(  long removed) throws DatabaseException {
    updateMemorySize(removed,0);
    original(removed);
  }
  protected void hook602(  long removed) throws DatabaseException {
    updateMemorySize(removed,0);
    original(removed);
  }
}
