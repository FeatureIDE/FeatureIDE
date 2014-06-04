package com.sleepycat.je.dbi;
public class MemoryBudget {
  private long criticalThreshold;
  public long getCriticalThreshold(){
    return criticalThreshold;
  }
  /** 
 * Update the environment wide tree memory count, wake up the evictor if
 * necessary.
 * @param incrementnote that increment may be negative.
 */
  public void updateTreeMemoryUsage(  long increment){
    original(increment);
    if (getCacheMemoryUsage() > cacheBudget) {
      envImpl.alertEvictor();
    }
  }
  /** 
 * Update the environment wide misc memory count, wake up the evictor if
 * necessary.
 * @param incrementnote that increment may be negative.
 */
  public void updateMiscMemoryUsage(  long increment){
    original(increment);
    if (getCacheMemoryUsage() > cacheBudget) {
      envImpl.alertEvictor();
    }
  }
  public void updateLockMemoryUsage(  long increment,  int lockTableIndex){
    original(increment,lockTableIndex);
    if (getCacheMemoryUsage() > cacheBudget) {
      envImpl.alertEvictor();
    }
  }
@MethodObject static class MemoryBudget_reset {
    protected void hook349() throws DatabaseException {
      _this.criticalThreshold=newCriticalThreshold;
      original();
    }
  }
}
