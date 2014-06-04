package com.sleepycat.je.txn;
public class TxnManager {
  protected void hook820(  StatsConfig config,  TransactionStats stats) throws DatabaseException {
    allTxnLatch.acquire();
    try {
      original(config,stats);
    }
  finally {
      allTxnLatch.release();
    }
  }
}
