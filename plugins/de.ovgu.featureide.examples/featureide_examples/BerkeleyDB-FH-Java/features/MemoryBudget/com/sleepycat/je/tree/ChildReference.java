package com.sleepycat.je.tree;
public class ChildReference {
  protected void hook613(  IN in) throws DatabaseException, LogFileNotFoundException, Exception {
    if (in != null) {
      in.updateMemorySize(null,target);
    }
    original(in);
  }
}
