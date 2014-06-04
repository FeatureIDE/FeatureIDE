package com.sleepycat.je.cleaner;
public class Cleaner {
  protected void hook85(  DatabaseId id){
    Tracer.trace(detailedTraceLevel,env,"CleanAddPendingDB " + id);
    original(id);
  }
}
