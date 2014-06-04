package com.sleepycat.je.cleaner;
import com.sleepycat.je.dbi.MemoryBudget;
import de.ovgu.cide.jakutil.*;
/** 
 * Delta file summary info for a tracked file.  Tracked files are managed by
 * the UtilizationTracker.
 * <p>The methods in this class for reading obsolete offsets may be used by
 * multiple threads without synchronization even while another thread is adding
 * offsets.  This is possible because elements are never deleted from the
 * lists.  The thread adding obsolete offsets does so under the log write
 * latch to prevent multiple threads from adding concurrently.</p>
 */
public class TrackedFileSummary extends FileSummary {
  private UtilizationTracker tracker;
  private long fileNum;
  private OffsetList obsoleteOffsets;
  private boolean trackDetail;
  private boolean allowFlush=true;
  /** 
 * Creates an empty tracked summary.
 */
  TrackedFileSummary(  UtilizationTracker tracker,  long fileNum,  boolean trackDetail){
    this.tracker=tracker;
    this.fileNum=fileNum;
    this.trackDetail=trackDetail;
  }
  /** 
 * Returns whether this summary is allowed or prohibited from being flushed
 * or evicted during cleaning.  By default, flushing is allowed.
 */
  public boolean getAllowFlush(){
    return allowFlush;
  }
  /** 
 * Allows or prohibits this summary from being flushed or evicted during
 * cleaning.  By default, flushing is allowed.
 */
  void setAllowFlush(  boolean allowFlush){
    this.allowFlush=allowFlush;
  }
  /** 
 * Returns the file number being tracked.
 */
  public long getFileNumber(){
    return fileNum;
  }
  /** 
 * Overrides reset for a tracked file, and is called when a FileSummaryLN
 * is written to the log.
 * <p>Must be called under the log write latch.</p>
 */
  public void reset(){
    obsoleteOffsets=null;
    tracker.resetFile(this);
    this.hook168();
    super.reset();
  }
  /** 
 * Tracks the given offset as obsolete or non-obsolete.
 * <p>Must be called under the log write latch.</p>
 */
  void trackObsolete(  long offset){
    new TrackedFileSummary_trackObsolete(this,offset).execute();
  }
  /** 
 * Adds the obsolete offsets as well as the totals of the given object.
 */
  void addTrackedSummary(  TrackedFileSummary other){
    add(other);
    if (other.obsoleteOffsets != null) {
      if (obsoleteOffsets != null) {
        if (obsoleteOffsets.merge(other.obsoleteOffsets)) {
          this.hook169();
        }
      }
 else {
        obsoleteOffsets=other.obsoleteOffsets;
      }
    }
  }
  /** 
 * Returns obsolete offsets as an array of longs, or null if none.
 */
  public long[] getObsoleteOffsets(){
    if (obsoleteOffsets != null) {
      return obsoleteOffsets.toArray();
    }
 else {
      return null;
    }
  }
  /** 
 * Returns whether the given offset is present in the tracked offsets.
 * This does not indicate whether the offset is obsolete in general, but
 * only if it is known to be obsolete in this version of the tracked
 * information.
 */
  boolean containsObsoleteOffset(  long offset){
    if (obsoleteOffsets != null) {
      return obsoleteOffsets.contains(offset);
    }
 else {
      return false;
    }
  }
@MethodObject static class TrackedFileSummary_trackObsolete {
    TrackedFileSummary_trackObsolete(    TrackedFileSummary _this,    long offset){
      this._this=_this;
      this.offset=offset;
    }
    void execute(){
      if (!_this.trackDetail) {
        return;
      }
      this.hook170();
      if (_this.obsoleteOffsets == null) {
        _this.obsoleteOffsets=new OffsetList();
        this.hook171();
      }
      if (_this.obsoleteOffsets.add(offset,_this.tracker.getEnvironment().isOpen())) {
        this.hook172();
      }
    }
    protected TrackedFileSummary _this;
    protected long offset;
    protected int adjustMem;
    protected void hook170(){
    }
    protected void hook171(){
    }
    protected void hook172(){
    }
  }
  protected void hook168(){
  }
  protected void hook169(){
  }
}
