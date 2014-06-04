package com.sleepycat.je.tree;
public class BINDelta {
  protected void hook611(  BIN fullBIN) throws DatabaseException {
    fullBIN.releaseLatch();
    original(fullBIN);
  }
  protected void hook612(  BIN fullBIN) throws DatabaseException {
    fullBIN.latch();
    original(fullBIN);
  }
}
