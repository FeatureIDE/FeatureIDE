package com.sleepycat.je.incomp;
public class INCompressor {
  protected void hook390(  BIN bin) throws DatabaseException {
    bin.releaseLatch();
    original(bin);
  }
}
