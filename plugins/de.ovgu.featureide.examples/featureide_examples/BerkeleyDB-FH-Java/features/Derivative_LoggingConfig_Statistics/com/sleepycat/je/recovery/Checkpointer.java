package com.sleepycat.je.recovery;
public class Checkpointer {
  protected void hook516(  StringBuffer sb){
    sb.append(" nFullINFlushThisRun=").append(nFullINFlushThisRun);
    sb.append(" nDeltaINFlushThisRun=").append(nDeltaINFlushThisRun);
    original(sb);
  }
}
