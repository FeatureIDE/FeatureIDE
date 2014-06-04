package com.sleepycat.je.tree;
public class IN {
  protected void hook615(  String msg){
    Tracer.trace(Level.INFO,databaseImpl.getDbEnvironment(),msg);
    original(msg);
  }
}
