package com.sleepycat.je.cleaner;
public class Cleaner {
  protected void hook88(  long fileNumValue) throws DatabaseException {
    Tracer.trace(Level.SEVERE,env,"Cleaner deleted file 0x" + Long.toHexString(fileNumValue));
    original(fileNumValue);
  }
  private void traceFileNotDeleted(  Exception e,  long fileNum){
    Tracer.trace(env,"Cleaner","deleteSafeToDeleteFiles","Log file 0x" + Long.toHexString(fileNum) + " could not be "+ (expunge ? "deleted" : "renamed")+ ".  This operation will be retried at the next checkpoint.",e);
    original(e,fileNum);
  }
  protected void hook89(  DatabaseException DBE) throws DatabaseException {
    Tracer.trace(env,"com.sleepycat.je.cleaner.Cleaner","processLN","Exception thrown: ",DBE);
    original(DBE);
  }
}
