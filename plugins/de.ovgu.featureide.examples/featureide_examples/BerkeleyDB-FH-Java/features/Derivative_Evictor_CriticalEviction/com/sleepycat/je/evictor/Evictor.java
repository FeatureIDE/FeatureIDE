package com.sleepycat.je.evictor;
public class Evictor {
  /** 
 * Do a check on whether synchronous eviction is needed.
 */
  public void doCriticalEviction() throws DatabaseException {
    new Evictor_doCriticalEviction(this).execute();
  }
@MethodObject static class Evictor_doCriticalEviction {
    Evictor_doCriticalEviction(    Evictor _this){
      this._this=_this;
    }
    void execute() throws DatabaseException {
    }
    protected Evictor _this;
    protected MemoryBudget mb;
    protected long currentUsage;
    protected long maxMem;
    protected long over;
  }
}
