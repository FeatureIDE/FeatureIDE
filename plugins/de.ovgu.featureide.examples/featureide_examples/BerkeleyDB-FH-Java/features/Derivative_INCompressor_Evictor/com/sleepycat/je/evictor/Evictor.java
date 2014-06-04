package com.sleepycat.je.evictor;
public class Evictor {
  protected void hook385(  IN target) throws DatabaseException {
    envImpl.lazyCompress(target);
    original(target);
  }
}
