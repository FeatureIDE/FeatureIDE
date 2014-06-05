package com.sleepycat.je.txn;
public class Txn {
  protected void hook803() throws DatabaseException, RunRecoveryException, Throwable {
    if ((deleteInfo != null) && deleteInfo.size() > 0) {
      envImpl.addToCompressorQueue(deleteInfo.values(),false);
      deleteInfo.clear();
    }
    original();
  }
  protected void hook804() throws DatabaseException {
    deleteInfo=null;
    original();
  }
}
