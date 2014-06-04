package com.sleepycat.je.dbi;
public class INList {
  private boolean updateMemoryUsage;
  INList(  EnvironmentImpl envImpl){
    updateMemoryUsage=true;
  }
  /** 
 * Used only by tree verifier when validating INList. Must be called with
 * orig.majorLatch acquired.
 */
  INList(  INList orig,  EnvironmentImpl envImpl) throws DatabaseException {
    updateMemoryUsage=false;
  }
  protected void hook346(  IN in) throws DatabaseException {
    if (updateMemoryUsage) {
      envImpl.getMemoryBudget().updateTreeMemoryUsage(in.getAccumulatedDelta() - in.getInMemorySize());
      in.setInListResident(false);
    }
    original(in);
  }
  /** 
 * Clear the entire list during recovery and at shutdown.
 */
  public void clear() throws DatabaseException {
    original();
    if (updateMemoryUsage) {
      envImpl.getMemoryBudget().refreshTreeMemoryUsage(0);
    }
  }
@MethodObject static class INList_addAndSetMemory {
    void execute(){
      original();
      if (_this.updateMemoryUsage) {
        mb=_this.envImpl.getMemoryBudget();
        mb.updateTreeMemoryUsage(in.getInMemorySize());
        in.setInListResident(true);
      }
    }
  }
}
