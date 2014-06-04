package com.sleepycat.je.recovery;
public class RecoveryManager {
  protected void hook573() throws DatabaseException, IOException {
    Tracer.trace(Level.INFO,env,"There are " + preparedTxns.size() + " prepared but unfinished txns.");
    original();
  }
  protected void hook574(  LNFileReader reader) throws IOException, DatabaseException, Exception {
    Tracer.trace(Level.INFO,env,"Found unfinished prepare record: id: " + reader.getTxnPrepareId() + " Xid: "+ reader.getTxnPrepareXid());
    original(reader);
  }
}
