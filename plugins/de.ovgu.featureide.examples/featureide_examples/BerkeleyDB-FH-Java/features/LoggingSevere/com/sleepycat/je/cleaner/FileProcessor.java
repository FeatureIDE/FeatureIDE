package com.sleepycat.je.cleaner;
class FileProcessor {
  protected void hook122(  IOException IOE) throws DatabaseException {
    Tracer.trace(env,"Cleaner","doClean","",IOE);
    original(IOE);
  }
  protected void hook123(  String traceMsg) throws DatabaseException {
    Tracer.trace(Level.SEVERE,env,traceMsg);
    original(traceMsg);
  }
}
