package com.sleepycat.je.dbi;
public class SortedLSNTreeWalker {
@MethodObject static class SortedLSNTreeWalker_extractINsForDb {
    protected void hook356() throws DatabaseException {
      inList.latchMajor();
      original();
    }
    protected void hook357() throws DatabaseException {
      inList.latchMinorAndDumpAddedINs();
      original();
    }
    protected void hook358() throws DatabaseException {
      inList.releaseMajorLatch();
      original();
    }
  }
}
