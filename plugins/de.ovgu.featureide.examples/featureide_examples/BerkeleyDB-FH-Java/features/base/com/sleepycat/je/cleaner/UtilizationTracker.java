package com.sleepycat.je.cleaner;
import java.util.ArrayList;
import java.util.List;
import com.sleepycat.je.DatabaseException;
import com.sleepycat.je.dbi.EnvironmentImpl;
import com.sleepycat.je.dbi.MemoryBudget;
import com.sleepycat.je.log.LogEntryType;
import com.sleepycat.je.utilint.DbLsn;
import de.ovgu.cide.jakutil.*;
/** 
 * Tracks changes to the utilization profile since the last checkpoint.
 * <p>
 * All changes to this object occur must under the log write latch. It is
 * possible to read tracked info without holding the latch. This is done by the
 * cleaner when selecting a file and by the checkpointer when determining what
 * FileSummaryLNs need to be written. To read tracked info outside the log write
 * latch, call getTrackedFile or getTrackedFiles. activateCleaner can also be
 * called outside the latch.
 * </p>
 */
public class UtilizationTracker {
  private EnvironmentImpl env;
  private Cleaner cleaner;
  private List files;
  private long activeFile;
  private TrackedFileSummary[] snapshot;
  private long bytesSinceActivate;
  /** 
 * Creates an empty tracker. The cleaner field of the environment object
 * must be initialized before using this constructor.
 */
  public UtilizationTracker(  EnvironmentImpl env) throws DatabaseException {
    this(env,env.getCleaner());
  }
  /** 
 * Constructor used by the cleaner constructor, prior to setting the cleaner
 * field of the environment.
 */
  UtilizationTracker(  EnvironmentImpl env,  Cleaner cleaner) throws DatabaseException {
    assert cleaner != null;
    this.env=env;
    this.cleaner=cleaner;
    files=new ArrayList();
    snapshot=new TrackedFileSummary[0];
    activeFile=-1;
  }
  public EnvironmentImpl getEnvironment(){
    return env;
  }
  /** 
 * Wakeup the cleaner thread and reset the log byte counter.
 */
  public void activateCleaner(){
    env.getCleaner().wakeup();
    bytesSinceActivate=0;
  }
  /** 
 * Returns a snapshot of the files being tracked as of the last time a log
 * entry was added. The summary info returned is the delta since the last
 * checkpoint, not the grand totals, and is approximate since it is changing
 * in real time. This method may be called without holding the log write
 * latch.
 * <p>
 * If files are added or removed from the list of tracked files in real
 * time, the returned array will not be changed since it is a snapshot. But
 * the objects contained in the array are live and will be updated in real
 * time under the log write latch. The array and the objects in the array
 * should not be modified by the caller.
 * </p>
 */
  public TrackedFileSummary[] getTrackedFiles(){
    return snapshot;
  }
  /** 
 * Returns one file from the snapshot of tracked files, or null if the given
 * file number is not in the snapshot array.
 * @see #getTrackedFiles
 */
  public TrackedFileSummary getTrackedFile(  long fileNum){
    TrackedFileSummary[] a=snapshot;
    for (int i=0; i < a.length; i+=1) {
      if (a[i].getFileNumber() == fileNum) {
        return a[i];
      }
    }
    return null;
  }
  /** 
 * Counts the addition of all new log entries including LNs, and returns
 * whether the cleaner should be woken.
 * <p>
 * Must be called under the log write latch.
 * </p>
 */
  public boolean countNewLogEntry(  long lsn,  LogEntryType type,  int size){
    TrackedFileSummary file=getFile(DbLsn.getFileNumber(lsn));
    file.totalCount+=1;
    file.totalSize+=size;
    if (type.isNodeType()) {
      if (inArray(type,LogEntryType.IN_TYPES)) {
        file.totalINCount+=1;
        file.totalINSize+=size;
      }
 else {
        file.totalLNCount+=1;
        file.totalLNSize+=size;
      }
    }
    bytesSinceActivate+=size;
    return (bytesSinceActivate >= env.getCleaner().cleanerBytesInterval);
  }
  /** 
 * Counts a node that has become obsolete and tracks the LSN offset to avoid
 * a lookup during cleaning.
 * <p>
 * This method should only be called for LNs and INs (i.e, only for nodes).
 * If type is null we assume it is an LN.
 * </p>
 * <p>
 * Must be called under the log write latch.
 * </p>
 */
  public void countObsoleteNode(  long lsn,  LogEntryType type){
    TrackedFileSummary file=getFile(DbLsn.getFileNumber(lsn));
    countOneNode(file,type);
    file.trackObsolete(DbLsn.getFileOffset(lsn));
  }
  /** 
 * Counts as countObsoleteNode does, but since the LSN may be inexact, does
 * not track the obsolete LSN offset.
 * <p>
 * This method should only be called for LNs and INs (i.e, only for nodes).
 * If type is null we assume it is an LN.
 * </p>
 * <p>
 * Must be called under the log write latch.
 * </p>
 */
  public void countObsoleteNodeInexact(  long lsn,  LogEntryType type){
    TrackedFileSummary file=getFile(DbLsn.getFileNumber(lsn));
    countOneNode(file,type);
  }
  /** 
 * Counts a change in the obsolete status of an node, incrementing the
 * obsolete count if obsolete is true and decrementing it if obsolete is
 * false.
 */
  private void countOneNode(  TrackedFileSummary file,  LogEntryType type){
    if (type == null || type.isNodeType()) {
      if (type == null || !inArray(type,LogEntryType.IN_TYPES)) {
        file.obsoleteLNCount+=1;
      }
 else {
        file.obsoleteINCount+=1;
      }
    }
  }
  /** 
 * Adds changes from a given TrackedFileSummary.
 * <p>
 * Must be called under the log write latch.
 * </p>
 */
  public void addSummary(  long fileNumber,  TrackedFileSummary other){
    TrackedFileSummary file=getFile(fileNumber);
    file.addTrackedSummary(other);
  }
  /** 
 * Returns a tracked summary for the given file which will not be flushed.
 * Used for watching changes that occur while a file is being cleaned.
 */
  public TrackedFileSummary getUnflushableTrackedSummary(  long fileNum) throws DatabaseException {
    TrackedFileSummary file=getFile(fileNum);
    file.setAllowFlush(false);
    return file;
  }
  /** 
 * Returns a tracked file for the given file number, adding an empty one if
 * the file is not already being tracked.
 * <p>
 * Must be called under the log write latch.
 * </p>
 */
  private TrackedFileSummary getFile(  long fileNum){
    if (activeFile < fileNum) {
      activeFile=fileNum;
    }
    int size=files.size();
    for (int i=0; i < size; i+=1) {
      TrackedFileSummary file=(TrackedFileSummary)files.get(i);
      if (file.getFileNumber() == fileNum) {
        return file;
      }
    }
    TrackedFileSummary file=new TrackedFileSummary(this,fileNum,cleaner.trackDetail);
    files.add(file);
    takeSnapshot();
    return file;
  }
  /** 
 * Called after the FileSummaryLN is written to the log during checkpoint.
 * <p>
 * We keep the active file summary in the tracked file list, but we remove
 * older files to prevent unbounded growth of the list.
 * </p>
 * <p>
 * Must be called under the log write latch.
 * </p>
 */
  void resetFile(  TrackedFileSummary file){
    if (file.getFileNumber() < activeFile && file.getAllowFlush()) {
      files.remove(file);
      takeSnapshot();
    }
  }
  /** 
 * Takes a snapshot of the tracked file list.
 * <p>
 * Must be called under the log write latch.
 * </p>
 */
  private void takeSnapshot(){
    TrackedFileSummary[] a=new TrackedFileSummary[files.size()];
    files.toArray(a);
    snapshot=a;
  }
  /** 
 * Returns whether an object reference is in an array.
 */
  private boolean inArray(  Object o,  Object[] a){
    for (int i=0; i < a.length; i+=1) {
      if (a[i] == o) {
        return true;
      }
    }
    return false;
  }
}
