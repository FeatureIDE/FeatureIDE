package com.sleepycat.je.cleaner;
public class Cleaner {
  protected void hook95(  BIN bin,  DIN parentDIN) throws DatabaseException {
    if (parentDIN != null) {
      parentDIN.releaseLatchIfOwner();
    }
    if (bin != null) {
      bin.releaseLatchIfOwner();
    }
    original(bin,parentDIN);
  }
}
