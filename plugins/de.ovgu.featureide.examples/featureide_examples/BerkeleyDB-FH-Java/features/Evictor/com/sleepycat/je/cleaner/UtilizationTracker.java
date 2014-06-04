package com.sleepycat.je.cleaner;
public class UtilizationTracker {
  /** 
 * Evicts tracked detail if the budget for the tracker is exceeded. Evicts
 * only one file summary LN at most to keep eviction batches small. Returns
 * the number of bytes freed.
 * <p>
 * When flushFileSummary is called, the TrackedFileSummary is cleared via
 * its reset method, which is called by FileSummaryLN.writeToLog. This is
 * how memory is subtracted from the budget.
 * </p>
 */
  public long evictMemory() throws DatabaseException {
    return new UtilizationTracker_evictMemory(this).execute();
  }
@MethodObject static class UtilizationTracker_evictMemory {
    UtilizationTracker_evictMemory(    UtilizationTracker _this){
      this._this=_this;
    }
    long execute() throws DatabaseException {
      if (!_this.cleaner.trackDetail) {
        return 0;
      }
      if (!_this.env.isOpen()) {
        return 0;
      }
      mb=_this.env.getMemoryBudget();
      totalEvicted=0;
      totalBytes=0;
      largestBytes=0;
      bestFile=null;
      a=_this.snapshot;
      for (int i=0; i < a.length; i+=1) {
        tfs=a[i];
        this.hook198();
        b1=tfs.getAllowFlush();
        this.hook197();
        if (b1) {
          this.hook199();
          bestFile=tfs;
        }
      }
      b2=bestFile != null;
      this.hook196();
      if (b2) {
        _this.env.getUtilizationProfile().flushFileSummary(bestFile);
        totalEvicted+=largestBytes;
      }
      return totalEvicted;
    }
    protected UtilizationTracker _this;
    protected MemoryBudget mb;
    protected long totalEvicted;
    protected long totalBytes;
    protected int largestBytes;
    protected TrackedFileSummary bestFile;
    protected TrackedFileSummary[] a;
    protected TrackedFileSummary tfs;
    protected int mem;
    protected boolean b1;
    protected boolean b2;
    protected void hook196() throws DatabaseException {
    }
    protected void hook197() throws DatabaseException {
    }
    protected void hook198() throws DatabaseException {
    }
    protected void hook199() throws DatabaseException {
    }
  }
}
