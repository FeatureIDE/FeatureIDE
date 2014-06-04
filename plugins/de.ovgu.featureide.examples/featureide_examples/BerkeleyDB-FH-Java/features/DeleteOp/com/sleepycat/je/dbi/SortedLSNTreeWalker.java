package com.sleepycat.je.dbi;
public class SortedLSNTreeWalker {
  protected void hook359() throws DatabaseException {
    if (setDbState) {
      dbImpl.finishedINListHarvest();
    }
    original();
  }
}
