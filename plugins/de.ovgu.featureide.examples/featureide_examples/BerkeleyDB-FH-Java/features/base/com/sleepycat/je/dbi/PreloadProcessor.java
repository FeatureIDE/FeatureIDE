package com.sleepycat.je.dbi;
import com.sleepycat.je.PreloadStats;
import com.sleepycat.je.dbi.SortedLSNTreeWalker.TreeNodeProcessor;
import com.sleepycat.je.log.LogEntryType;
import com.sleepycat.je.utilint.DbLsn;
import de.ovgu.cide.jakutil.*;
class PreloadProcessor implements TreeNodeProcessor {
  private EnvironmentImpl envImpl;
  private long maxBytes;
  private long targetTime;
  PreloadProcessor(  EnvironmentImpl envImpl,  long maxBytes,  long targetTime,  PreloadStats stats){
    this.envImpl=envImpl;
    this.maxBytes=maxBytes;
    this.targetTime=targetTime;
    this.hook353(stats);
  }
  /** 
 * Called for each LSN that the SortedLSNTreeWalker encounters.
 */
  public void processLSN(  long childLsn,  LogEntryType childType){
    assert childLsn != DbLsn.NULL_LSN;
    if (System.currentTimeMillis() > targetTime) {
      throw DatabaseImpl.timeExceededPreloadException;
    }
    this.hook355();
    this.hook354(childType);
  }
  protected void hook353(  PreloadStats stats){
  }
  protected void hook354(  LogEntryType childType){
  }
  protected void hook355(){
  }
}
