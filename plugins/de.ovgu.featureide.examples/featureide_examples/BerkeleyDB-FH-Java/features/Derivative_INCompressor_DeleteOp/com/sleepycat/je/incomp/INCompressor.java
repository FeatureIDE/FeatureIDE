package com.sleepycat.je.incomp;
public class INCompressor {
  protected boolean hook415(  BINSearch binSearch,  boolean close) throws DatabaseException {
    close|=binSearch.db.isDeleted();
    return original(binSearch,close);
  }
}
