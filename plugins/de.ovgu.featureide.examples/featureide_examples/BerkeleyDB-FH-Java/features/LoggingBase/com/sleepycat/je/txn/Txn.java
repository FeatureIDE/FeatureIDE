package com.sleepycat.je.txn;
public class Txn {
@MethodObject static class Txn_traceCommit {
    void execute(){
      logger=envImpl.getLogger();
      original();
    }
  }
}
