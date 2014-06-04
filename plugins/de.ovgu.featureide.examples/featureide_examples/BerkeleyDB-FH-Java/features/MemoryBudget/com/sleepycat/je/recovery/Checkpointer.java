package com.sleepycat.je.recovery;
public class Checkpointer {
@MethodObject static class Checkpointer_selectDirtyINs {
    protected void hook553() throws DatabaseException {
      totalSize=0;
      mb=_this.envImpl.getMemoryBudget();
      original();
    }
    protected void hook554() throws DatabaseException {
      mb.refreshTreeMemoryUsage(totalSize);
      original();
    }
    protected void hook530() throws DatabaseException {
      totalSize=mb.accumulateNewUsage(in,totalSize);
      original();
    }
  }
@MethodObject static class Checkpointer_doCheckpoint {
    protected void hook548() throws DatabaseException {
      dirtyMapMemSize=0;
      original();
    }
    protected void hook549() throws DatabaseException {
      mb.updateMiscMemoryUsage(0 - dirtyMapMemSize);
      original();
    }
    protected void hook550() throws DatabaseException {
      mb.updateMiscMemoryUsage(totalSize);
      original();
    }
    protected void hook551() throws DatabaseException {
      totalSize=0;
      original();
    }
    protected void hook552() throws DatabaseException {
      size=nodeSet.size() * MemoryBudget.CHECKPOINT_REFERENCE_SIZE;
      totalSize+=size;
      dirtyMapMemSize+=size;
      original();
    }
  }
}
