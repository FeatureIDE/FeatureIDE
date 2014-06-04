package com.sleepycat.je;
import java.io.Serializable;
import com.sleepycat.je.utilint.DbLsn;
import de.ovgu.cide.jakutil.*;
/** 
 * Javadoc for this public class is generated
 * via the doc templates in the doc_src directory.
 */
public class EnvironmentStats implements Serializable {
  /** 
 * The number of bins encountered by the INCompressor that were split
 * between the time they were put on the compressor queue and when
 * the compressor ran.
 */
  private int splitBins;
  /** 
 * The number of bins encountered by the INCompressor that had their
 * database closed between the time they were put on the
 * compressor queue and when the compressor ran.
 */
  private int dbClosedBins;
  /** 
 * The number of bins encountered by the INCompressor that had cursors
 * referring to them when the compressor ran.
 */
  private int cursorsBins;
  /** 
 * The number of bins encountered by the INCompressor that were
 * not actually empty when the compressor ran.
 */
  private int nonEmptyBins;
  /** 
 * The number of bins that were successfully processed by the IN
 * Compressor.
 */
  private int processedBins;
  /** 
 * The number of entries in the INCompressor queue when the getStats()
 * call was made.
 */
  private int inCompQueueSize;
  /** 
 * The number of passes made to the evictor.
 */
  private int nEvictPasses;
  /** 
 * The accumulated number of nodes selected to evict.
 */
  private long nNodesSelected;
  /** 
 * The accumulated number of nodes scanned in order to select the
 * eviction set.
 */
  private long nNodesScanned;
  /** 
 * The accumulated number of nodes evicted.
 */
  private long nNodesExplicitlyEvicted;
  /** 
 * The number of BINs stripped by the evictor.
 */
  private long nBINsStripped;
  /** 
 * The number of bytes we need to evict in order to get under budget.
 */
  private long requiredEvictBytes;
  /** 
 * The total number of checkpoints run so far.
 */
  private int nCheckpoints;
  /** 
 * The Id of the last checkpoint.
 */
  private long lastCheckpointId;
  /** 
 * The accumulated number of full INs flushed to the log.
 */
  private int nFullINFlush;
  /** 
 * The accumulated number of full BINs flushed to the log.
 */
  private int nFullBINFlush;
  /** 
 * The accumulated number of Delta INs flushed to the log.
 */
  private int nDeltaINFlush;
  /** 
 * The location in the log of the last checkpoint start.
 */
  private long lastCheckpointStart;
  /** 
 * The location in the log of the last checkpoint end.
 */
  private long lastCheckpointEnd;
  /** 
 * The number of files to be cleaned to reach the target utilization. 
 */
  private int cleanerBacklog;
  /** 
 * The number of cleaner runs this session. 
 */
  private int nCleanerRuns;
  /** 
 * The number of cleaner file deletions this session. 
 */
  private int nCleanerDeletions;
  /** 
 * The accumulated number of INs obsolete.
 */
  private int nINsObsolete;
  /** 
 * The accumulated number of INs cleaned.
 */
  private int nINsCleaned;
  /** 
 * The accumulated number of INs that were not found in the tree anymore
 * (deleted).
 */
  private int nINsDead;
  /** 
 * The accumulated number of INs migrated.
 */
  private int nINsMigrated;
  /** 
 * The accumulated number of LNs obsolete.
 */
  private int nLNsObsolete;
  /** 
 * The accumulated number of LNs cleaned.
 */
  private int nLNsCleaned;
  /** 
 * The accumulated number of LNs that were not found in the tree anymore
 * (deleted).
 */
  private int nLNsDead;
  /** 
 * The accumulated number of LNs encountered that were locked.
 */
  private int nLNsLocked;
  /** 
 * The accumulated number of LNs encountered that were migrated forward
 * in the log.
 */
  private int nLNsMigrated;
  /** 
 * The accumulated number of LNs that were marked for migration during
 * cleaning.
 */
  private int nLNsMarked;
  /** 
 * The accumulated number of LNs processed without a tree lookup.
 */
  private int nLNQueueHits;
  /** 
 * The accumulated number of LNs processed because they were previously
 * locked.
 */
  private int nPendingLNsProcessed;
  /** 
 * The accumulated number of LNs processed because they were previously
 * marked for migration.
 */
  private int nMarkedLNsProcessed;
  /** 
 * The accumulated number of LNs processed because they are soon to be
 * cleaned.
 */
  private int nToBeCleanedLNsProcessed;
  /** 
 * The accumulated number of LNs processed because they qualify for
 * clustering.
 */
  private int nClusterLNsProcessed;
  /** 
 * The accumulated number of pending LNs that could not be locked for
 * migration because of a long duration application lock.
 */
  private int nPendingLNsLocked;
  /** 
 * The accumulated number of log entries read by the cleaner.
 */
  private int nCleanerEntriesRead;
  private long cacheDataBytes;
  private long nNotResident;
  private long nCacheMiss;
  private int nLogBuffers;
  private long bufferBytes;
  private long nRepeatFaultReads;
  private long nTempBufferWrites;
  private long nRepeatIteratorReads;
  /** 
 * Internal use only.
 */
  public EnvironmentStats(){
    reset();
  }
  /** 
 * Resets all stats.
 */
  private void reset(){
    splitBins=0;
    dbClosedBins=0;
    cursorsBins=0;
    nonEmptyBins=0;
    processedBins=0;
    inCompQueueSize=0;
    nEvictPasses=0;
    nNodesSelected=0;
    nNodesScanned=0;
    nNodesExplicitlyEvicted=0;
    nBINsStripped=0;
    requiredEvictBytes=0;
    nCheckpoints=0;
    lastCheckpointId=0;
    nFullINFlush=0;
    nFullBINFlush=0;
    nDeltaINFlush=0;
    lastCheckpointStart=DbLsn.NULL_LSN;
    lastCheckpointEnd=DbLsn.NULL_LSN;
    cleanerBacklog=0;
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
    nCleanerEntriesRead=0;
    cacheDataBytes=0;
    nNotResident=0;
    nCacheMiss=0;
    nLogBuffers=0;
    bufferBytes=0;
    this.hook60();
    nRepeatFaultReads=0;
    nTempBufferWrites=0;
    nRepeatIteratorReads=0;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public long getBufferBytes(){
    return bufferBytes;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public int getCursorsBins(){
    return cursorsBins;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public int getDbClosedBins(){
    return dbClosedBins;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public int getInCompQueueSize(){
    return inCompQueueSize;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public long getLastCheckpointId(){
    return lastCheckpointId;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public long getNCacheMiss(){
    return nCacheMiss;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public int getNCheckpoints(){
    return nCheckpoints;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public int getCleanerBacklog(){
    return cleanerBacklog;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public int getNCleanerRuns(){
    return nCleanerRuns;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public int getNCleanerDeletions(){
    return nCleanerDeletions;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public int getNDeltaINFlush(){
    return nDeltaINFlush;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public long getLastCheckpointEnd(){
    return lastCheckpointEnd;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public long getLastCheckpointStart(){
    return lastCheckpointStart;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public int getNCleanerEntriesRead(){
    return nCleanerEntriesRead;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public int getNEvictPasses(){
    return nEvictPasses;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public int getNFullINFlush(){
    return nFullINFlush;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public int getNFullBINFlush(){
    return nFullBINFlush;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public int getNINsObsolete(){
    return nINsObsolete;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public int getNINsCleaned(){
    return nINsCleaned;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public int getNINsDead(){
    return nINsDead;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public int getNINsMigrated(){
    return nINsMigrated;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public int getNLNsObsolete(){
    return nLNsObsolete;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public int getNLNsCleaned(){
    return nLNsCleaned;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public int getNLNsDead(){
    return nLNsDead;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public int getNLNsLocked(){
    return nLNsLocked;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public int getNLNsMigrated(){
    return nLNsMigrated;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public int getNLNsMarked(){
    return nLNsMarked;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public int getNLNQueueHits(){
    return nLNQueueHits;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public int getNPendingLNsProcessed(){
    return nPendingLNsProcessed;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public int getNMarkedLNsProcessed(){
    return nMarkedLNsProcessed;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public int getNToBeCleanedLNsProcessed(){
    return nToBeCleanedLNsProcessed;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public int getNClusterLNsProcessed(){
    return nClusterLNsProcessed;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public int getNPendingLNsLocked(){
    return nPendingLNsLocked;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public int getNLogBuffers(){
    return nLogBuffers;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public long getNNodesExplicitlyEvicted(){
    return nNodesExplicitlyEvicted;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public long getNBINsStripped(){
    return nBINsStripped;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public long getRequiredEvictBytes(){
    return requiredEvictBytes;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public long getNNodesScanned(){
    return nNodesScanned;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public long getNNodesSelected(){
    return nNodesSelected;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public long getCacheTotalBytes(){
    return cacheDataBytes + bufferBytes;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public long getCacheDataBytes(){
    return cacheDataBytes;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public long getNNotResident(){
    return nNotResident;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public int getNonEmptyBins(){
    return nonEmptyBins;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public int getProcessedBins(){
    return processedBins;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public long getNRepeatFaultReads(){
    return nRepeatFaultReads;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public long getNTempBufferWrites(){
    return nTempBufferWrites;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public long getNRepeatIteratorReads(){
    return nRepeatIteratorReads;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public int getSplitBins(){
    return splitBins;
  }
  /** 
 * Internal use only.
 */
  public void setCacheDataBytes(  long cacheDataBytes){
    this.cacheDataBytes=cacheDataBytes;
  }
  /** 
 * Internal use only.
 */
  public void setNNotResident(  long nNotResident){
    this.nNotResident=nNotResident;
  }
  /** 
 * Internal use only.
 */
  public void setNCacheMiss(  long nCacheMiss){
    this.nCacheMiss=nCacheMiss;
  }
  /** 
 * Internal use only.
 */
  public void setNLogBuffers(  int nLogBuffers){
    this.nLogBuffers=nLogBuffers;
  }
  /** 
 * Internal use only.
 */
  public void setBufferBytes(  long bufferBytes){
    this.bufferBytes=bufferBytes;
  }
  /** 
 * Internal use only.
 */
  public void setCursorsBins(  int val){
    cursorsBins=val;
  }
  /** 
 * Internal use only.
 */
  public void setDbClosedBins(  int val){
    dbClosedBins=val;
  }
  /** 
 * Internal use only.
 */
  public void setInCompQueueSize(  int val){
    inCompQueueSize=val;
  }
  /** 
 * Internal use only.
 */
  public void setLastCheckpointId(  long l){
    lastCheckpointId=l;
  }
  /** 
 * Internal use only.
 */
  public void setNCheckpoints(  int val){
    nCheckpoints=val;
  }
  /** 
 * Internal use only.
 */
  public void setCleanerBacklog(  int val){
    cleanerBacklog=val;
  }
  /** 
 * Internal use only.
 */
  public void setNCleanerRuns(  int val){
    nCleanerRuns=val;
  }
  /** 
 * Internal use only.
 */
  public void setNCleanerDeletions(  int val){
    nCleanerDeletions=val;
  }
  /** 
 * Internal use only.
 */
  public void setNDeltaINFlush(  int val){
    nDeltaINFlush=val;
  }
  /** 
 * Internal use only.
 */
  public void setLastCheckpointEnd(  long lsn){
    lastCheckpointEnd=lsn;
  }
  /** 
 * Internal use only.
 */
  public void setLastCheckpointStart(  long lsn){
    lastCheckpointStart=lsn;
  }
  /** 
 * Internal use only.
 */
  public void setNCleanerEntriesRead(  int val){
    nCleanerEntriesRead=val;
  }
  /** 
 * Internal use only.
 */
  public void setNEvictPasses(  int val){
    nEvictPasses=val;
  }
  /** 
 * Internal use only.
 */
  public void setNFullINFlush(  int val){
    nFullINFlush=val;
  }
  /** 
 * Internal use only.
 */
  public void setNFullBINFlush(  int val){
    nFullBINFlush=val;
  }
  /** 
 * Internal use only.
 */
  public void setNINsObsolete(  int val){
    nINsObsolete=val;
  }
  /** 
 * Internal use only.
 */
  public void setNINsCleaned(  int val){
    nINsCleaned=val;
  }
  /** 
 * Internal use only.
 */
  public void setNINsDead(  int val){
    nINsDead=val;
  }
  /** 
 * Internal use only.
 */
  public void setNINsMigrated(  int val){
    nINsMigrated=val;
  }
  /** 
 * Internal use only.
 */
  public void setNLNsObsolete(  int val){
    nLNsObsolete=val;
  }
  /** 
 * Internal use only.
 */
  public void setNLNsCleaned(  int val){
    nLNsCleaned=val;
  }
  /** 
 * Internal use only.
 */
  public void setNLNsDead(  int val){
    nLNsDead=val;
  }
  /** 
 * Internal use only.
 */
  public void setNLNsLocked(  int val){
    nLNsLocked=val;
  }
  /** 
 * Internal use only.
 */
  public void setNLNsMigrated(  int val){
    nLNsMigrated=val;
  }
  /** 
 * Internal use only.
 */
  public void setNLNsMarked(  int val){
    nLNsMarked=val;
  }
  /** 
 * Internal use only.
 */
  public void setNLNQueueHits(  int val){
    nLNQueueHits=val;
  }
  /** 
 * Internal use only.
 */
  public void setNPendingLNsProcessed(  int val){
    nPendingLNsProcessed=val;
  }
  /** 
 * Internal use only.
 */
  public void setNMarkedLNsProcessed(  int val){
    nMarkedLNsProcessed=val;
  }
  /** 
 * Internal use only.
 */
  public void setNToBeCleanedLNsProcessed(  int val){
    nToBeCleanedLNsProcessed=val;
  }
  /** 
 * Internal use only.
 */
  public void setNClusterLNsProcessed(  int val){
    nClusterLNsProcessed=val;
  }
  /** 
 * Internal use only.
 */
  public void setNPendingLNsLocked(  int val){
    nPendingLNsLocked=val;
  }
  /** 
 * Internal use only.
 */
  public void setNNodesExplicitlyEvicted(  long l){
    nNodesExplicitlyEvicted=l;
  }
  /** 
 * Internal use only.
 */
  public void setRequiredEvictBytes(  long l){
    requiredEvictBytes=l;
  }
  /** 
 * Internal use only.
 */
  public void setNBINsStripped(  long l){
    nBINsStripped=l;
  }
  /** 
 * Internal use only.
 */
  public void setNNodesScanned(  long l){
    nNodesScanned=l;
  }
  /** 
 * Internal use only.
 */
  public void setNNodesSelected(  long l){
    nNodesSelected=l;
  }
  /** 
 * Internal use only.
 */
  public void setNonEmptyBins(  int val){
    nonEmptyBins=val;
  }
  /** 
 * Internal use only.
 */
  public void setProcessedBins(  int val){
    processedBins=val;
  }
  /** 
 * Internal use only.
 */
  public void setNRepeatFaultReads(  long val){
    nRepeatFaultReads=val;
  }
  /** 
 * Internal use only.
 */
  public void setNTempBufferWrites(  long val){
    nTempBufferWrites=val;
  }
  /** 
 * Internal use only.
 */
  public void setNRepeatIteratorReads(  long val){
    nRepeatIteratorReads=val;
  }
  /** 
 * Internal use only.
 */
  public void setSplitBins(  int val){
    splitBins=val;
  }
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public String toString(){
    StringBuffer sb=new StringBuffer();
    sb.append("splitBins=").append(splitBins).append('\n');
    sb.append("dbClosedBins=").append(dbClosedBins).append('\n');
    sb.append("cursorsBins=").append(cursorsBins).append('\n');
    sb.append("nonEmptyBins=").append(nonEmptyBins).append('\n');
    sb.append("processedBins=").append(processedBins).append('\n');
    sb.append("inCompQueueSize=").append(inCompQueueSize).append('\n');
    sb.append("nEvictPasses=").append(nEvictPasses).append('\n');
    sb.append("nNodesSelected=").append(nNodesSelected).append('\n');
    sb.append("nNodesScanned=").append(nNodesScanned).append('\n');
    sb.append("nNodesExplicitlyEvicted=").append(nNodesExplicitlyEvicted).append('\n');
    sb.append("nBINsStripped=").append(nBINsStripped).append('\n');
    sb.append("requiredEvictBytes=").append(requiredEvictBytes).append('\n');
    sb.append("nCheckpoints=").append(nCheckpoints).append('\n');
    sb.append("lastCheckpointId=").append(lastCheckpointId).append('\n');
    sb.append("nFullINFlush=").append(nFullINFlush).append('\n');
    sb.append("nFullBINFlush=").append(nFullBINFlush).append('\n');
    sb.append("nDeltaINFlush=").append(nDeltaINFlush).append('\n');
    sb.append("lastCheckpointStart=").append(DbLsn.getNoFormatString(lastCheckpointStart)).append('\n');
    sb.append("lastCheckpointEnd=").append(DbLsn.getNoFormatString(lastCheckpointEnd)).append('\n');
    sb.append("cleanerBacklog=").append(cleanerBacklog).append('\n');
    sb.append("nCleanerRuns=").append(nCleanerRuns).append('\n');
    sb.append("nCleanerDeletions=").append(nCleanerDeletions).append('\n');
    sb.append("nINsObsolete=").append(nINsObsolete).append('\n');
    sb.append("nINsCleaned=").append(nINsCleaned).append('\n');
    sb.append("nINsDead=").append(nINsDead).append('\n');
    sb.append("nINsMigrated=").append(nINsMigrated).append('\n');
    sb.append("nLNsObsolete=").append(nLNsObsolete).append('\n');
    sb.append("nLNsCleaned=").append(nLNsCleaned).append('\n');
    sb.append("nLNsDead=").append(nLNsDead).append('\n');
    sb.append("nLNsLocked=").append(nLNsLocked).append('\n');
    sb.append("nLNsMigrated=").append(nLNsMigrated).append('\n');
    sb.append("nLNsMarked=").append(nLNsMarked).append('\n');
    sb.append("nLNQueueHits=").append(nLNQueueHits).append('\n');
    sb.append("nPendingLNsProcessed=").append(nPendingLNsProcessed).append('\n');
    sb.append("nMarkedLNsProcessed=").append(nMarkedLNsProcessed).append('\n');
    sb.append("nToBeCleanedLNsProcessed=").append(nToBeCleanedLNsProcessed).append('\n');
    sb.append("nClusterLNsProcessed=").append(nClusterLNsProcessed).append('\n');
    sb.append("nPendingLNsLocked=").append(nPendingLNsLocked).append('\n');
    sb.append("nCleanerEntriesRead=").append(nCleanerEntriesRead).append('\n');
    sb.append("nNotResident=").append(nNotResident).append('\n');
    sb.append("nCacheMiss=").append(nCacheMiss).append('\n');
    sb.append("nLogBuffers=").append(nLogBuffers).append('\n');
    sb.append("bufferBytes=").append(bufferBytes).append('\n');
    sb.append("cacheDataBytes=").append(cacheDataBytes).append('\n');
    sb.append("cacheTotalBytes=").append(getCacheTotalBytes()).append('\n');
    this.hook61(sb);
    sb.append("nRepeatFaultReads=").append(nRepeatFaultReads).append('\n');
    sb.append("nTempBufferWrite=").append(nTempBufferWrites).append('\n');
    sb.append("nRepeatIteratorReads=").append(nRepeatIteratorReads).append('\n');
    return sb.toString();
  }
  protected void hook60(){
  }
  protected void hook61(  StringBuffer sb){
  }
}
