package com.sleepycat.je.cleaner;
public class Cleaner {
  protected void hook87(  Set safeFiles) throws DatabaseException {
    Tracer.trace(Level.SEVERE,env,"Cleaner has " + safeFiles.size() + " files not deleted because of read-only processes.");
    original(safeFiles);
  }
}
