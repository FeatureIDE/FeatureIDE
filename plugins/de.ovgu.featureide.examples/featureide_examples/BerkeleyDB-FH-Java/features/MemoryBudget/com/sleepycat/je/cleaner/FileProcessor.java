package com.sleepycat.je.cleaner;
class FileProcessor {
@MethodObject static class FileProcessor_processFile {
    protected void hook118() throws DatabaseException, IOException {
    }
    protected void hook161() throws DatabaseException, IOException {
      adjustMem=(2 * readBufferSize) + obsoleteOffsets.getLogSize();
      budget=_this.env.getMemoryBudget();
{
        this.hook118();
        budget.updateMiscMemoryUsage(adjustMem);
      }
      original();
    }
    protected void hook162() throws DatabaseException, IOException {
      budget.updateMiscMemoryUsage(0 - adjustMem);
      original();
    }
  }
}
