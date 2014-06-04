package com.sleepycat.je.cleaner;
public class TrackedFileSummary {
  private int memSize;
  /** 
 * Return the total memory size for this object.  We only bother to budget
 * obsolete detail, not the overhead for this object, for two reasons:
 * 1) The number of these objects is very small, and 2) unit tests disable
 * detail tracking as a way to prevent budget adjustments here.
 */
  int getMemorySize(){
    return memSize;
  }
  private void updateMemoryBudget(  int delta){
    memSize+=delta;
    tracker.getEnvironment().getMemoryBudget().updateMiscMemoryUsage(delta);
  }
  protected void hook168(){
    if (memSize > 0) {
      updateMemoryBudget(0 - memSize);
    }
    original();
  }
  protected void hook169(){
    updateMemoryBudget(-MemoryBudget.TFS_LIST_SEGMENT_OVERHEAD);
    original();
  }
@MethodObject static class TrackedFileSummary_trackObsolete {
    void execute(){
      original();
      if (adjustMem != 0) {
        _this.updateMemoryBudget(adjustMem);
      }
    }
    protected void hook170(){
      adjustMem=0;
      original();
    }
    protected void hook171(){
      adjustMem+=MemoryBudget.TFS_LIST_INITIAL_OVERHEAD;
      original();
    }
    protected void hook172(){
      adjustMem+=MemoryBudget.TFS_LIST_SEGMENT_OVERHEAD;
      original();
    }
  }
}
