package com.sleepycat.je.cleaner;
class FileProcessor {
  protected void hook121(  String traceMsg) throws DatabaseException, IOException {
    Tracer.trace(Level.INFO,env,traceMsg);
    original(traceMsg);
  }
}
