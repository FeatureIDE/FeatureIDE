package com.sleepycat.je.dbi;
public class DbTree {
  protected boolean hook292(  VerifyConfig config,  PrintStream out,  boolean ret) throws DatabaseException {
synchronized (envImpl.getINCompressor()) {
      ret=original(config,out,ret);
    }
    return ret;
  }
}
