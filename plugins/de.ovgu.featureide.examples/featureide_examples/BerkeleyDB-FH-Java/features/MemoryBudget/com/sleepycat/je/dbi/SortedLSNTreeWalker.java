package com.sleepycat.je.dbi;
public class SortedLSNTreeWalker {
@MethodObject static class SortedLSNTreeWalker_extractINsForDb {
    boolean execute() throws DatabaseException {
      boolean result=original();
      mb.updateTreeMemoryUsage(memoryChange);
      return result;
    }
    protected void hook360() throws DatabaseException {
      memoryChange=0;
      mb=_this.envImpl.getMemoryBudget();
      original();
    }
    protected void hook361() throws DatabaseException {
      memoryChange+=(thisIN.getAccumulatedDelta() - thisIN.getInMemorySize());
      thisIN.setInListResident(false);
      original();
    }
    protected void hook362() throws DatabaseException {
      mb.updateTreeMemoryUsage(memoryChange);
      original();
    }
  }
}
