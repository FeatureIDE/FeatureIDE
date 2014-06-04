package com.sleepycat.je.dbi;
import com.sleepycat.je.latch.Latch;
import com.sleepycat.je.latch.LatchSupport;
import com.sleepycat.je.latch.SharedLatch;
import com.sleepycat.je.log.LatchedLogManager;
public class EnvironmentImpl {
  private static boolean fairLatches;
  private Latch mapTreeRootLatch;
  private SharedLatch triggerLatch;
  public static boolean getFairLatches(){
    return fairLatches;
  }
  /** 
 * Returns the shared trigger latch.
 */
  public SharedLatch getTriggerLatch(){
    return triggerLatch;
  }
  protected void hook320() throws DatabaseException {
    triggerLatch=LatchSupport.makeSharedLatch("TriggerLatch",this);
    original();
  }
  protected void hook321() throws DatabaseException {
    if (fairLatches) {
      logManager=new LatchedLogManager(this,isReadOnly);
    }
 else {
      original();
    }
  }
  protected void hook322() throws DatabaseException {
    fairLatches=configManager.getBoolean(EnvironmentParams.ENV_FAIR_LATCHES);
    original();
  }
  protected void hook323() throws DatabaseException {
    mapTreeRootLatch=LatchSupport.makeLatch("MapTreeRoot",this);
    original();
  }
  /** 
 * Log the map tree root and save the LSN.
 */
  public void logMapTreeRoot() throws DatabaseException {
    mapTreeRootLatch.acquire();
    try {
      original();
    }
  finally {
      mapTreeRootLatch.release();
    }
  }
  /** 
 * Force a rewrite of the map tree root if required.
 */
  public void rewriteMapTreeRoot(  long cleanerTargetLsn) throws DatabaseException {
    mapTreeRootLatch.acquire();
    try {
      original(cleanerTargetLsn);
    }
  finally {
      mapTreeRootLatch.release();
    }
  }
  protected void hook324(  long rootLsn) throws DatabaseException {
    mapTreeRootLatch.acquire();
    try {
      original(rootLsn);
    }
  finally {
      mapTreeRootLatch.release();
    }
  }
}
