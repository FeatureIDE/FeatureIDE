package com.sleepycat.je.txn;
public class Txn {
  protected void hook800(  Throwable t) throws DatabaseException, Throwable {
    Tracer.trace(envImpl,"Txn","commit","Commit of transaction " + id + " failed",t);
    original(t);
  }
  protected void hook801(  Long nodeId,  long undoLsn,  DatabaseException e) throws DatabaseException {
    Tracer.trace(envImpl,"Txn","undo","for node=" + nodeId + " LSN="+ DbLsn.getNoFormatString(undoLsn),e);
    original(nodeId,undoLsn,e);
  }
}
