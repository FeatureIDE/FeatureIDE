package com.sleepycat.je.recovery;
public class RecoveryManager {
  protected void hook575(  IOException e) throws DatabaseException {
    Tracer.trace(env,"RecoveryManager","recover","Couldn't recover",e);
    original(e);
  }
  protected void hook576(  DatabaseImpl db,  long logLsn,  Exception e,  String trace) throws DatabaseException {
    Tracer.trace(db.getDbEnvironment(),"RecoveryManager","replaceOrInsert"," lsnFromLog:" + DbLsn.getNoFormatString(logLsn) + " "+ trace,e);
    original(db,logLsn,e,trace);
  }
  protected void hook577(  String method,  Exception origException,  String badLsnString) throws DatabaseException {
    Tracer.trace(env,"RecoveryManager",method,"last LSN = " + badLsnString,origException);
    original(method,origException,badLsnString);
  }
}
