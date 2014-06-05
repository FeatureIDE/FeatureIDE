package com.sleepycat.je.dbi;
public class EnvironmentImpl {
  public boolean verify(  VerifyConfig config,  PrintStream out) throws DatabaseException {
    return dbMapTree.verify(config,out);
  }
}
