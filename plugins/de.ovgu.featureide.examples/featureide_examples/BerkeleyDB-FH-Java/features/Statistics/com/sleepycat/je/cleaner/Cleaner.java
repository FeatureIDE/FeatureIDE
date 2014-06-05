package com.sleepycat.je.cleaner;
import com.sleepycat.je.EnvironmentStats;
import com.sleepycat.je.StatsConfig;
public class Cleaner {
  int nBacklogFiles=0;
  int nCleanerDeletions=0;
  int nINsObsolete=0;
  int nINsCleaned=0;
  int nINsDead=0;
  int nINsMigrated=0;
  int nLNsObsolete=0;
  int nLNsCleaned=0;
  int nLNsDead=0;
  int nLNsLocked=0;
  int nLNsMigrated=0;
  int nLNsMarked=0;
  int nLNQueueHits=0;
  int nPendingLNsProcessed=0;
  int nMarkedLNsProcessed=0;
  int nToBeCleanedLNsProcessed=0;
  int nClusterLNsProcessed=0;
  int nPendingLNsLocked=0;
  int nEntriesRead=0;
  long nRepeatIteratorReads=0;
  /** 
 * Load stats.
 */
  public void loadStats(  StatsConfig config,  EnvironmentStats stat) throws DatabaseException {
    stat.setCleanerBacklog(nBacklogFiles);
    stat.setNCleanerRuns(nCleanerRuns);
    stat.setNCleanerDeletions(nCleanerDeletions);
    stat.setNINsObsolete(nINsObsolete);
    stat.setNINsCleaned(nINsCleaned);
    stat.setNINsDead(nINsDead);
    stat.setNINsMigrated(nINsMigrated);
    stat.setNLNsObsolete(nLNsObsolete);
    stat.setNLNsCleaned(nLNsCleaned);
    stat.setNLNsDead(nLNsDead);
    stat.setNLNsLocked(nLNsLocked);
    stat.setNLNsMigrated(nLNsMigrated);
    stat.setNLNsMarked(nLNsMarked);
    stat.setNLNQueueHits(nLNQueueHits);
    stat.setNPendingLNsProcessed(nPendingLNsProcessed);
    stat.setNMarkedLNsProcessed(nMarkedLNsProcessed);
    stat.setNToBeCleanedLNsProcessed(nToBeCleanedLNsProcessed);
    stat.setNClusterLNsProcessed(nClusterLNsProcessed);
    stat.setNPendingLNsLocked(nPendingLNsLocked);
    stat.setNCleanerEntriesRead(nEntriesRead);
    stat.setNRepeatIteratorReads(nRepeatIteratorReads);
    if (config.getClear()) {
      nCleanerRuns=0;
      nCleanerDeletions=0;
      nINsObsolete=0;
      nINsCleaned=0;
      nINsDead=0;
      nINsMigrated=0;
      nLNsObsolete=0;
      nLNsCleaned=0;
      nLNsDead=0;
      nLNsLocked=0;
      nLNsMigrated=0;
      nLNsMarked=0;
      nLNQueueHits=0;
      nPendingLNsProcessed=0;
      nMarkedLNsProcessed=0;
      nToBeCleanedLNsProcessed=0;
      nClusterLNsProcessed=0;
      nPendingLNsLocked=0;
      nEntriesRead=0;
      nRepeatIteratorReads=0;
    }
  }
  protected void hook96() throws DatabaseException {
    nCleanerDeletions++;
    original();
  }
  /** 
 * Update the lowUtilizationFiles and mustBeCleanedFiles fields with new
 * read-only collections, and update the backlog file count.
 */
  public void updateReadOnlyFileCollections(){
    original();
    nBacklogFiles=fileSelector.getBacklog();
  }
  protected void hook97() throws DatabaseException {
    nPendingLNsProcessed++;
    original();
  }
  protected void hook98() throws DatabaseException {
    nLNsDead++;
    original();
  }
  protected void hook99() throws DatabaseException {
    nPendingLNsLocked++;
    original();
  }
  protected void hook100() throws DatabaseException {
    nLNsDead++;
    original();
  }
  protected void hook101(){
    nMarkedLNsProcessed++;
    original();
  }
  protected void hook102(){
    nToBeCleanedLNsProcessed++;
    original();
  }
  protected void hook103(){
    nClusterLNsProcessed++;
    original();
  }
  protected void hook104() throws DatabaseException {
    nLNsMigrated++;
    original();
  }
  protected void hook105(  boolean wasCleaned) throws DatabaseException {
    if (wasCleaned) {
      nLNsDead++;
    }
    original(wasCleaned);
  }
  protected void hook106(  boolean wasCleaned) throws DatabaseException {
    if (wasCleaned) {
      nLNsLocked++;
    }
    original(wasCleaned);
  }
  protected void hook107(  boolean wasCleaned) throws DatabaseException {
    if (wasCleaned) {
      nLNsDead++;
    }
    original(wasCleaned);
  }
  protected void hook108(  boolean wasCleaned) throws DatabaseException {
    if (wasCleaned) {
      nLNsDead++;
    }
    original(wasCleaned);
  }
  protected void hook109() throws DatabaseException {
    nLNsMigrated++;
    original();
  }
  protected void hook110(  boolean wasCleaned) throws DatabaseException {
    if (wasCleaned) {
      nLNsLocked++;
    }
    original(wasCleaned);
  }
  protected void hook111(  boolean wasCleaned) throws DatabaseException {
    if (wasCleaned) {
      nLNsDead++;
    }
    original(wasCleaned);
  }
}
