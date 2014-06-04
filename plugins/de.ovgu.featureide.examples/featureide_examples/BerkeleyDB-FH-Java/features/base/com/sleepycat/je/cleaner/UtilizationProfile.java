package com.sleepycat.je.cleaner;
import java.io.File;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Iterator;
import java.util.List;
import java.util.Set;
import java.util.SortedMap;
import java.util.SortedSet;
import java.util.StringTokenizer;
import java.util.TreeMap;
import java.util.logging.Level;
import com.sleepycat.je.DatabaseConfig;
import com.sleepycat.je.DatabaseEntry;
import com.sleepycat.je.DatabaseException;
import com.sleepycat.je.DbInternal;
import com.sleepycat.je.OperationStatus;
import com.sleepycat.je.TransactionConfig;
import com.sleepycat.je.config.EnvironmentParams;
import com.sleepycat.je.dbi.CursorImpl;
import com.sleepycat.je.dbi.DatabaseId;
import com.sleepycat.je.dbi.DatabaseImpl;
import com.sleepycat.je.dbi.DbConfigManager;
import com.sleepycat.je.dbi.DbTree;
import com.sleepycat.je.dbi.EnvConfigObserver;
import com.sleepycat.je.dbi.EnvironmentImpl;
import com.sleepycat.je.dbi.MemoryBudget;
import com.sleepycat.je.dbi.CursorImpl.SearchMode;
import com.sleepycat.je.log.FileManager;
import com.sleepycat.je.log.entry.LNLogEntry;
import com.sleepycat.je.tree.BIN;
import com.sleepycat.je.tree.FileSummaryLN;
import com.sleepycat.je.tree.Tree;
import com.sleepycat.je.tree.TreeLocation;
import com.sleepycat.je.txn.AutoTxn;
import com.sleepycat.je.txn.BasicLocker;
import com.sleepycat.je.txn.LockType;
import com.sleepycat.je.txn.Locker;
import com.sleepycat.je.utilint.DbLsn;
import de.ovgu.cide.jakutil.*;
/** 
 * The UP tracks utilization summary information for all log files.
 * <p>Unlike the UtilizationTracker, the UP is not accessed under the log write
 * latch and is instead synchronized on itself for protecting the cache.  It is
 * not accessed during the primary data access path, except for when flushing
 * (writing) file summary LNs.  This occurs in the following cases:
 * <ol>
 * <li>The summary information is flushed at the end of a checkpoint.  This
 * allows tracking to occur in memory in between checkpoints, and replayed
 * during recovery.</li>
 * <li>When committing the truncateDatabase and removeDatabase operations, the
 * summary information is flushed because detail tracking for those operations
 * is not replayed during recovery</li>
 * <li>The evictor will ask the UtilizationTracker to flush the largest summary
 * if the memory taken by the tracker exeeds its budget.</li>
 * </ol>
 * <p>The cache is populated by the RecoveryManager just before performing the
 * initial checkpoint.  The UP must be open and populated in order to respond
 * to requests to flush summaries and to evict tracked detail, even if the
 * cleaner is disabled.</p>
 * <p>WARNING: While synchronized on this object, eviction is not permitted.
 * If it were, this could cause deadlocks because the order of locking would be
 * the UP object and then the evictor.  During normal eviction the order is to
 * first lock the evictor and then the UP, when evicting tracked detail.</p>
 * <p>The methods in this class synchronize to protect the cached summary
 * information.  Some methods also access the UP database.  However, because
 * eviction must not occur while synchronized, UP database access is not
 * performed while synchronized except in one case: when inserting a new
 * summary record.  In that case we disallow eviction during the database
 * operation.</p>
 */
public class UtilizationProfile implements EnvConfigObserver {
  private EnvironmentImpl env;
  private UtilizationTracker tracker;
  private DatabaseImpl fileSummaryDb;
  private SortedMap fileSummaryMap;
  private boolean cachePopulated;
  private boolean rmwFixEnabled;
  /** 
 * Minimum overall utilization threshold that triggers cleaning.  Is
 * non-private for unit tests.
 */
  int minUtilization;
  /** 
 * Minimum utilization threshold for an individual log file that triggers
 * cleaning.  Is non-private for unit tests.
 */
  int minFileUtilization;
  /** 
 * Minumum age to qualify for cleaning.  If the first active LSN file is 5
 * and the mininum age is 2, file 4 won't qualify but file 3 will.  Must be
 * greater than zero because we never clean the first active LSN file.  Is
 * non-private for unit tests.
 */
  int minAge;
  /** 
 * An array of pairs of file numbers, where each pair is a range of files
 * to be force cleaned.  Index i is the from value and i+1 is the to value,
 * both inclusive.
 */
  private long[] forceCleanFiles;
  /** 
 * Creates an empty UP.
 */
  public UtilizationProfile(  EnvironmentImpl env,  UtilizationTracker tracker) throws DatabaseException {
    this.env=env;
    this.tracker=tracker;
    fileSummaryMap=new TreeMap();
    rmwFixEnabled=env.getConfigManager().getBoolean(EnvironmentParams.CLEANER_RMW_FIX);
    parseForceCleanFiles(env.getConfigManager().get(EnvironmentParams.CLEANER_FORCE_CLEAN_FILES));
    envConfigUpdate(env.getConfigManager());
    env.addConfigObserver(this);
  }
  /** 
 * Process notifications of mutable property changes.
 */
  public void envConfigUpdate(  DbConfigManager cm) throws DatabaseException {
    minAge=cm.getInt(EnvironmentParams.CLEANER_MIN_AGE);
    minUtilization=cm.getInt(EnvironmentParams.CLEANER_MIN_UTILIZATION);
    minFileUtilization=cm.getInt(EnvironmentParams.CLEANER_MIN_FILE_UTILIZATION);
  }
  /** 
 * @see EnvironmentParams#CLEANER_RMW_FIX
 * @see FileSummaryLN#postFetchInit
 */
  public boolean isRMWFixEnabled(){
    return rmwFixEnabled;
  }
  /** 
 * Returns the number of files in the profile.
 */
  synchronized int getNumberOfFiles() throws DatabaseException {
    assert cachePopulated;
    return fileSummaryMap.size();
  }
  /** 
 * Returns the cheapest file to clean from the given list of files.  This
 * method is used to select the first file to be cleaned in the batch of
 * to-be-cleaned files.
 */
  synchronized Long getCheapestFileToClean(  SortedSet files) throws DatabaseException {
    if (files.size() == 1) {
      return (Long)files.first();
    }
    assert cachePopulated;
    Long bestFile=null;
    int bestCost=Integer.MAX_VALUE;
    for (Iterator iter=files.iterator(); iter.hasNext(); ) {
      Long file=(Long)iter.next();
      FileSummary summary=getFileSummary(file);
      int thisCost=summary.getNonObsoleteCount();
      if (bestFile == null || thisCost < bestCost) {
        bestFile=file;
        bestCost=thisCost;
      }
    }
    return bestFile;
  }
  /** 
 * Returns the best file that qualifies for cleaning, or null if no file
 * qualifies.
 * @param fileSelector is used to determine valid cleaning candidates.
 * @param forceCleaning is true to always select a file, even if its
 * utilization is above the minimum utilization threshold.
 * @param lowUtilizationFiles is a returned set of files that are below the
 * minimum utilization threshold.
 */
  synchronized Long getBestFileForCleaning(  FileSelector fileSelector,  boolean forceCleaning,  Set lowUtilizationFiles) throws DatabaseException {
    if (lowUtilizationFiles != null) {
      lowUtilizationFiles.clear();
    }
    assert cachePopulated;
    if (fileSummaryMap.size() == 0) {
      return null;
    }
    final int useMinUtilization=minUtilization;
    final int useMinFileUtilization=minFileUtilization;
    final int useMinAge=minAge;
    long firstActiveLsn=env.getCheckpointer().getFirstActiveLsn();
    if (firstActiveLsn == DbLsn.NULL_LSN) {
      return null;
    }
    Iterator iter=fileSummaryMap.keySet().iterator();
    Long bestFile=null;
    int bestUtilization=101;
    long totalSize=0;
    long totalObsoleteSize=0;
    while (iter.hasNext()) {
      Long file=(Long)iter.next();
      long fileNum=file.longValue();
      FileSummary summary=getFileSummary(file);
      int obsoleteSize=summary.getObsoleteSize();
      if (fileSelector.isFileCleaningInProgress(file)) {
        totalSize+=summary.totalSize - obsoleteSize;
        totalObsoleteSize+=estimateUPObsoleteSize(summary);
        continue;
      }
      totalSize+=summary.totalSize;
      totalObsoleteSize+=obsoleteSize;
      if (DbLsn.getFileNumber(firstActiveLsn) - fileNum < useMinAge) {
        continue;
      }
      int thisUtilization=utilization(obsoleteSize,summary.totalSize);
      if (bestFile == null || thisUtilization < bestUtilization) {
        bestFile=file;
        bestUtilization=thisUtilization;
      }
      if (lowUtilizationFiles != null && thisUtilization < useMinUtilization) {
        lowUtilizationFiles.add(file);
      }
    }
    int totalUtilization=utilization(totalObsoleteSize,totalSize);
    if (forceCleaning || totalUtilization < useMinUtilization || bestUtilization < useMinFileUtilization) {
      return bestFile;
    }
 else {
      return null;
    }
  }
  /** 
 * Calculate the utilization percentage.
 */
  public static int utilization(  long obsoleteSize,  long totalSize){
    if (totalSize != 0) {
      return (int)(((totalSize - obsoleteSize) * 100) / totalSize);
    }
 else {
      return 0;
    }
  }
  /** 
 * Estimate the log size that will be made obsolete when a log file is
 * deleted and we delete its UP records.
 * Note that we do not count the space taken by the deleted FileSummaryLN
 * records written during log file deletion.  These add the same amount to
 * the total log size and the obsolete log size, and therefore have a small
 * impact on total utilization.
 */
  private int estimateUPObsoleteSize(  FileSummary summary){
    if (true)     return 0;
    final int OVERHEAD=75;
    int OFFSETS_PER_LN=1000;
    int BYTES_PER_LN=OVERHEAD + (OFFSETS_PER_LN * 2);
    int totalNodes=summary.totalLNCount + summary.totalINCount;
    int logEntries=(totalNodes / OFFSETS_PER_LN) + 1;
    return logEntries * BYTES_PER_LN;
  }
  /** 
 * Gets the base summary from the cached map.  Add the tracked summary, if
 * one exists, to the base summary.  Sets all entries obsolete, if the file
 * is in the forceCleanFiles set.
 */
  private synchronized FileSummary getFileSummary(  Long file){
    FileSummary summary=(FileSummary)fileSummaryMap.get(file);
    long fileNum=file.longValue();
    TrackedFileSummary trackedSummary=tracker.getTrackedFile(fileNum);
    if (trackedSummary != null) {
      FileSummary totals=new FileSummary();
      totals.add(summary);
      totals.add(trackedSummary);
      summary=totals;
    }
    if (isForceCleanFile(fileNum)) {
      FileSummary allObsolete=new FileSummary();
      allObsolete.add(summary);
      allObsolete.obsoleteLNCount=allObsolete.totalLNCount;
      allObsolete.obsoleteINCount=allObsolete.totalINCount;
      summary=allObsolete;
    }
    return summary;
  }
  /** 
 * Returns whether the given file is in the forceCleanFiles set.
 */
  private boolean isForceCleanFile(  long file){
    if (forceCleanFiles != null) {
      for (int i=0; i < forceCleanFiles.length; i+=2) {
        long from=forceCleanFiles[i];
        long to=forceCleanFiles[i + 1];
        if (file >= from && file <= to) {
          return true;
        }
      }
    }
    return false;
  }
  /** 
 * Parses the je.cleaner.forceCleanFiles property value.
 */
  private void parseForceCleanFiles(  String propValue){
    if (propValue == null || propValue.length() == 0) {
      forceCleanFiles=null;
    }
 else {
      String errPrefix="Error in " + EnvironmentParams.CLEANER_FORCE_CLEAN_FILES.getName() + "="+ propValue+ ": ";
      StringTokenizer tokens=new StringTokenizer(propValue,",-",true);
      List list=new ArrayList();
      while (tokens.hasMoreTokens()) {
        String fromStr=tokens.nextToken();
        long fromNum;
        try {
          fromNum=Long.parseLong(fromStr,16);
        }
 catch (        NumberFormatException e) {
          throw new IllegalArgumentException(errPrefix + "Invalid hex file number: " + fromStr);
        }
        long toNum=-1;
        if (tokens.hasMoreTokens()) {
          String delim=tokens.nextToken();
          if (",".equals(delim)) {
            toNum=fromNum;
          }
 else           if ("-".equals(delim)) {
            if (tokens.hasMoreTokens()) {
              String toStr=tokens.nextToken();
              try {
                toNum=Long.parseLong(toStr,16);
              }
 catch (              NumberFormatException e) {
                throw new IllegalArgumentException(errPrefix + "Invalid hex file number: " + toStr);
              }
            }
 else {
              throw new IllegalArgumentException(errPrefix + "Expected file number: " + delim);
            }
          }
 else {
            throw new IllegalArgumentException(errPrefix + "Expected '-' or ',': " + delim);
          }
        }
 else {
          toNum=fromNum;
        }
        assert toNum != -1;
        list.add(new Long(fromNum));
        list.add(new Long(toNum));
      }
      forceCleanFiles=new long[list.size()];
      for (int i=0; i < forceCleanFiles.length; i+=1) {
        forceCleanFiles[i]=((Long)list.get(i)).longValue();
      }
    }
  }
  /** 
 * Count the given tracked info as obsolete and then log the summaries.
 */
  public void countAndLogSummaries(  TrackedFileSummary[] summaries) throws DatabaseException {
    env.getLogManager().countObsoleteNodes(summaries);
    if (!DbInternal.getCheckpointUP(env.getConfigManager().getEnvironmentConfig())) {
      return;
    }
    for (int i=0; i < summaries.length; i+=1) {
      long fileNum=summaries[i].getFileNumber();
      TrackedFileSummary tfs=tracker.getTrackedFile(fileNum);
      if (tfs != null) {
        flushFileSummary(tfs);
      }
    }
  }
  /** 
 * Returns a copy of the current file summary map, optionally including
 * tracked summary information, for use by the DbSpace utility and by unit
 * tests.  The returned map's key is a Long file number and its value is a
 * FileSummary.
 */
  public synchronized SortedMap getFileSummaryMap(  boolean includeTrackedFiles) throws DatabaseException {
    assert cachePopulated;
    if (includeTrackedFiles) {
      TreeMap map=new TreeMap();
      Iterator iter=fileSummaryMap.keySet().iterator();
      while (iter.hasNext()) {
        Long file=(Long)iter.next();
        FileSummary summary=getFileSummary(file);
        map.put(file,summary);
      }
      TrackedFileSummary[] trackedFiles=tracker.getTrackedFiles();
      for (int i=0; i < trackedFiles.length; i+=1) {
        TrackedFileSummary summary=trackedFiles[i];
        long fileNum=summary.getFileNumber();
        Long file=new Long(fileNum);
        if (!map.containsKey(file)) {
          map.put(file,summary);
        }
      }
      return map;
    }
 else {
      return new TreeMap(fileSummaryMap);
    }
  }
  /** 
 * Clears the cache of file summary info.  The cache starts out unpopulated
 * and is populated on the first call to getBestFileForCleaning.
 */
  public synchronized void clearCache(){
    new UtilizationProfile_clearCache(this).execute();
  }
  /** 
 * Removes a file from the utilization database and the profile, after it
 * has been deleted by the cleaner.
 */
  void removeFile(  Long fileNum) throws DatabaseException {
    new UtilizationProfile_removeFile(this,fileNum).execute();
  }
  /** 
 * For the LN at the cursor position deletes all LNs for the file.  This
 * method performs eviction and is not synchronized.
 */
  private void deleteFileSummary(  Long fileNum) throws DatabaseException {
    Locker locker=null;
    CursorImpl cursor=null;
    try {
      locker=new BasicLocker(env);
      cursor=new CursorImpl(fileSummaryDb,locker);
      DatabaseEntry keyEntry=new DatabaseEntry();
      DatabaseEntry dataEntry=new DatabaseEntry();
      long fileNumVal=fileNum.longValue();
      if (!getFirstFSLN(cursor,fileNumVal,keyEntry,dataEntry,LockType.WRITE)) {
        return;
      }
      OperationStatus status=OperationStatus.SUCCESS;
      while (status == OperationStatus.SUCCESS) {
        this.hook173();
        FileSummaryLN ln=(FileSummaryLN)cursor.getCurrentLN(LockType.NONE);
        if (ln != null) {
          if (fileNumVal != ln.getFileNumber(keyEntry.getData())) {
            break;
          }
          TrackedFileSummary tfs=tracker.getTrackedFile(fileNumVal);
          if (tfs != null) {
            ln.setTrackedSummary(tfs);
          }
          cursor.delete();
        }
        status=cursor.getNext(keyEntry,dataEntry,LockType.WRITE,true,false);
      }
    }
  finally {
      if (cursor != null) {
        this.hook178(cursor);
        cursor.close();
      }
      if (locker != null) {
        locker.operationEnd();
      }
    }
  }
  /** 
 * Updates and stores the FileSummary for a given tracked file, if flushing
 * of the summary is allowed.
 */
  public void flushFileSummary(  TrackedFileSummary tfs) throws DatabaseException {
    if (tfs.getAllowFlush()) {
      putFileSummary(tfs);
    }
  }
  /** 
 * Updates and stores the FileSummary for a given tracked file.  This
 * method is synchronized and may not perform eviction.
 */
  private synchronized PackedOffsets putFileSummary(  TrackedFileSummary tfs) throws DatabaseException {
    return new UtilizationProfile_putFileSummary(this,tfs).execute();
  }
  /** 
 * Returns the stored/packed obsolete offsets and the tracked obsolete
 * offsets for the given file.  The tracked summary object returned can be
 * used to test for obsolete offsets that are being added during cleaning
 * by other threads participating in lazy migration.  The caller must call
 * TrackedFileSummary.setAllowFlush(true) when cleaning is complete.
 * This method performs eviction and is not synchronized.
 * @param logUpdate if true, log any updates to the utilization profile. If
 * false, only retrieve the new information.
 */
  TrackedFileSummary getObsoleteDetail(  Long fileNum,  PackedOffsets packedOffsets,  boolean logUpdate) throws DatabaseException {
    if (!env.getCleaner().trackDetail) {
      return null;
    }
    assert cachePopulated;
    long fileNumVal=fileNum.longValue();
    List list=new ArrayList();
    TrackedFileSummary tfs=env.getLogManager().getUnflushableTrackedSummary(fileNumVal);
    Locker locker=null;
    CursorImpl cursor=null;
    try {
      locker=new BasicLocker(env);
      cursor=new CursorImpl(fileSummaryDb,locker);
      DatabaseEntry keyEntry=new DatabaseEntry();
      DatabaseEntry dataEntry=new DatabaseEntry();
      OperationStatus status=OperationStatus.SUCCESS;
      if (!getFirstFSLN(cursor,fileNumVal,keyEntry,dataEntry,LockType.NONE)) {
        status=OperationStatus.NOTFOUND;
      }
      while (status == OperationStatus.SUCCESS) {
        this.hook174();
        FileSummaryLN ln=(FileSummaryLN)cursor.getCurrentLN(LockType.NONE);
        if (ln != null) {
          if (fileNumVal != ln.getFileNumber(keyEntry.getData())) {
            break;
          }
          PackedOffsets offsets=ln.getObsoleteOffsets();
          if (offsets != null) {
            list.add(offsets.toArray());
          }
          this.hook187(cursor);
        }
        status=cursor.getNext(keyEntry,dataEntry,LockType.NONE,true,false);
      }
    }
  finally {
      this.hook179(cursor);
      if (locker != null) {
        locker.operationEnd();
      }
    }
    if (!tfs.isEmpty()) {
      PackedOffsets offsets=null;
      if (logUpdate) {
        offsets=putFileSummary(tfs);
        if (offsets != null) {
          list.add(offsets.toArray());
        }
      }
 else {
        long[] offsetList=tfs.getObsoleteOffsets();
        if (offsetList != null) {
          list.add(offsetList);
        }
      }
    }
    int size=0;
    for (int i=0; i < list.size(); i+=1) {
      long[] a=(long[])list.get(i);
      size+=a.length;
    }
    long[] offsets=new long[size];
    int index=0;
    for (int i=0; i < list.size(); i+=1) {
      long[] a=(long[])list.get(i);
      System.arraycopy(a,0,offsets,index,a.length);
      index+=a.length;
    }
    assert index == offsets.length;
    packedOffsets.pack(offsets);
    return tfs;
  }
  /** 
 * Populate the profile for file selection.  This method performs eviction
 * and is not synchronized.  It must be called before recovery is complete
 * so that synchronization is unnecessary.  It must be called before the
 * recovery checkpoint so that the checkpoint can flush file summary
 * information.
 */
  public boolean populateCache() throws DatabaseException {
    return new UtilizationProfile_populateCache(this).execute();
  }
  /** 
 * Positions at the most recent LN for the given file number.
 */
  private boolean getFirstFSLN(  CursorImpl cursor,  long fileNum,  DatabaseEntry keyEntry,  DatabaseEntry dataEntry,  LockType lockType) throws DatabaseException {
    byte[] keyBytes=FileSummaryLN.makePartialKey(fileNum);
    keyEntry.setData(keyBytes);
    int result=cursor.searchAndPosition(keyEntry,dataEntry,SearchMode.SET_RANGE,lockType);
    if ((result & CursorImpl.FOUND) == 0) {
      return false;
    }
    boolean exactKeyMatch=((result & CursorImpl.EXACT_KEY) != 0);
    if (exactKeyMatch && cursor.getCurrentAlreadyLatched(keyEntry,dataEntry,lockType,true) != OperationStatus.KEYEMPTY) {
      return true;
    }
    OperationStatus status=cursor.getNext(keyEntry,dataEntry,lockType,true,!exactKeyMatch);
    return status == OperationStatus.SUCCESS;
  }
  /** 
 * If the file summary db is already open, return, otherwise attempt to
 * open it.  If the environment is read-only and the database doesn't
 * exist, return false.  If the environment is read-write the database will
 * be created if it doesn't exist.
 */
  private boolean openFileSummaryDatabase() throws DatabaseException {
    if (fileSummaryDb != null) {
      return true;
    }
    DbTree dbTree=env.getDbMapTree();
    Locker autoTxn=null;
    boolean operationOk=false;
    try {
      autoTxn=new AutoTxn(env,new TransactionConfig());
      DatabaseImpl db=dbTree.getDb(autoTxn,DbTree.UTILIZATION_DB_NAME,null,true);
      if (db == null) {
        if (env.isReadOnly()) {
          return false;
        }
        db=dbTree.createDb(autoTxn,DbTree.UTILIZATION_DB_NAME,new DatabaseConfig(),null,true);
      }
      fileSummaryDb=db;
      operationOk=true;
      return true;
    }
  finally {
      if (autoTxn != null) {
        autoTxn.operationEnd(operationOk);
      }
    }
  }
  /** 
 * Insert the given LN with the given key values.  This method is
 * synchronized and may not perform eviction.
 */
  private synchronized void insertFileSummary(  FileSummaryLN ln,  long fileNum,  int sequence) throws DatabaseException {
    byte[] keyBytes=FileSummaryLN.makeFullKey(fileNum,sequence);
    Locker locker=null;
    CursorImpl cursor=null;
    try {
      locker=new BasicLocker(env);
      cursor=new CursorImpl(fileSummaryDb,locker);
      this.hook189(cursor);
      OperationStatus status=cursor.putLN(keyBytes,ln,false);
      this.hook177(fileNum,sequence,status);
      this.hook188(cursor);
    }
  finally {
      if (cursor != null) {
        cursor.close();
      }
      if (locker != null) {
        locker.operationEnd();
      }
    }
  }
  /** 
 * Checks that all FSLN offsets are indeed obsolete.  Assumes that the
 * system is quiesent (does not lock LNs).  This method is not synchronized
 * (because it doesn't access fileSummaryMap) and eviction is allowed.
 * @return true if no verification failures.
 */
  public boolean verifyFileSummaryDatabase() throws DatabaseException {
    DatabaseEntry key=new DatabaseEntry();
    DatabaseEntry data=new DatabaseEntry();
    openFileSummaryDatabase();
    Locker locker=null;
    CursorImpl cursor=null;
    boolean ok=true;
    try {
      locker=new BasicLocker(env);
      cursor=new CursorImpl(fileSummaryDb,locker);
      if (cursor.positionFirstOrLast(true,null)) {
        OperationStatus status=cursor.getCurrentAlreadyLatched(key,data,LockType.NONE,true);
        while (status == OperationStatus.SUCCESS) {
          this.hook175();
          FileSummaryLN ln=(FileSummaryLN)cursor.getCurrentLN(LockType.NONE);
          if (ln != null) {
            long fileNumVal=ln.getFileNumber(key.getData());
            PackedOffsets offsets=ln.getObsoleteOffsets();
            if (offsets != null) {
              long[] vals=offsets.toArray();
              for (int i=0; i < vals.length; i++) {
                long lsn=DbLsn.makeLsn(fileNumVal,vals[i]);
                if (!verifyLsnIsObsolete(lsn)) {
                  ok=false;
                }
              }
            }
            this.hook190(cursor);
            status=cursor.getNext(key,data,LockType.NONE,true,false);
          }
        }
      }
    }
  finally {
      if (cursor != null) {
        cursor.close();
      }
      if (locker != null) {
        locker.operationEnd();
      }
    }
    return ok;
  }
  private boolean verifyLsnIsObsolete(  long lsn) throws DatabaseException {
    try {
      Object o=env.getLogManager().getLogEntry(lsn);
      if (!(o instanceof LNLogEntry)) {
        return true;
      }
      LNLogEntry entry=(LNLogEntry)o;
      if (entry.getLN().isDeleted()) {
        return true;
      }
      DatabaseId dbId=entry.getDbId();
      DatabaseImpl db=env.getDbMapTree().getDb(dbId);
      boolean b=db == null;
      b=this.hook186(db,b);
      if (b) {
        return true;
      }
      BIN bin=null;
      this.hook180(lsn,entry,db,bin);
      throw ReturnHack.returnBoolean;
    }
 catch (    ReturnBoolean r) {
      return r.value;
    }
  }
@MethodObject static class UtilizationProfile_clearCache {
    UtilizationProfile_clearCache(    UtilizationProfile _this){
      this._this=_this;
    }
    void execute(){
      _this.fileSummaryMap=new TreeMap();
      _this.cachePopulated=false;
    }
    protected UtilizationProfile _this;
    protected int memorySize;
    protected MemoryBudget mb;
  }
@MethodObject static class UtilizationProfile_removeFile {
    UtilizationProfile_removeFile(    UtilizationProfile _this,    Long fileNum){
      this._this=_this;
      this.fileNum=fileNum;
    }
    void execute() throws DatabaseException {
synchronized (_this) {
        assert _this.cachePopulated;
        if (_this.fileSummaryMap.remove(fileNum) != null) {
          this.hook192();
        }
      }
      _this.deleteFileSummary(fileNum);
    }
    protected UtilizationProfile _this;
    protected Long fileNum;
    protected MemoryBudget mb;
    protected void hook192() throws DatabaseException {
    }
  }
@MethodObject static class UtilizationProfile_putFileSummary {
    UtilizationProfile_putFileSummary(    UtilizationProfile _this,    TrackedFileSummary tfs){
      this._this=_this;
      this.tfs=tfs;
    }
    PackedOffsets execute() throws DatabaseException {
      if (_this.env.isReadOnly()) {
        throw new DatabaseException("Cannot write file summary in a read-only environment");
      }
      if (tfs.isEmpty()) {
        return null;
      }
      if (!_this.cachePopulated) {
        return null;
      }
      fileNum=tfs.getFileNumber();
      fileNumLong=new Long(fileNum);
      summary=(FileSummary)_this.fileSummaryMap.get(fileNumLong);
      if (summary == null) {
        file=new File(_this.env.getFileManager().getFullFileName(fileNum,FileManager.JE_SUFFIX));
        if (!file.exists()) {
          return null;
        }
        summary=new FileSummary();
      }
      tmp=new FileSummary();
      tmp.add(summary);
      tmp.add(tfs);
      sequence=tmp.getEntriesCounted();
      ln=new FileSummaryLN(summary);
      ln.setTrackedSummary(tfs);
      _this.insertFileSummary(ln,fileNum,sequence);
      summary=ln.getBaseSummary();
      if (_this.fileSummaryMap.put(fileNumLong,summary) == null) {
        this.hook193();
      }
      return ln.getObsoleteOffsets();
    }
    protected UtilizationProfile _this;
    protected TrackedFileSummary tfs;
    protected long fileNum;
    protected Long fileNumLong;
    protected FileSummary summary;
    protected File file;
    protected FileSummary tmp;
    protected int sequence;
    protected FileSummaryLN ln;
    protected MemoryBudget mb;
    protected void hook193() throws DatabaseException {
    }
  }
@MethodObject static class UtilizationProfile_populateCache {
    UtilizationProfile_populateCache(    UtilizationProfile _this){
      this._this=_this;
    }
    boolean execute() throws DatabaseException {
      assert !_this.cachePopulated;
      if (!_this.openFileSummaryDatabase()) {
        return false;
      }
      this.hook194();
      existingFiles=_this.env.getFileManager().getAllFileNumbers();
      locker=null;
      cursor=null;
      try {
        locker=new BasicLocker(_this.env);
        cursor=new CursorImpl(_this.fileSummaryDb,locker);
        keyEntry=new DatabaseEntry();
        dataEntry=new DatabaseEntry();
        if (cursor.positionFirstOrLast(true,null)) {
          status=cursor.getCurrentAlreadyLatched(keyEntry,dataEntry,LockType.NONE,true);
          if (status != OperationStatus.SUCCESS) {
            status=cursor.getNext(keyEntry,dataEntry,LockType.NONE,true,false);
          }
          while (status == OperationStatus.SUCCESS) {
            this.hook176();
            ln=(FileSummaryLN)cursor.getCurrentLN(LockType.NONE);
            if (ln == null) {
              status=cursor.getNext(keyEntry,dataEntry,LockType.NONE,true,false);
              continue;
            }
            keyBytes=keyEntry.getData();
            isOldVersion=ln.hasStringKey(keyBytes);
            fileNum=ln.getFileNumber(keyBytes);
            fileNumLong=new Long(fileNum);
            if (Arrays.binarySearch(existingFiles,fileNumLong) >= 0) {
              _this.fileSummaryMap.put(fileNumLong,ln.getBaseSummary());
              if (isOldVersion) {
                _this.insertFileSummary(ln,fileNum,0);
                this.hook182();
                cursor.delete();
                this.hook181();
              }
 else {
                this.hook191();
              }
            }
 else {
              _this.fileSummaryMap.remove(fileNumLong);
              if (isOldVersion) {
                this.hook184();
                cursor.delete();
                this.hook183();
              }
 else {
                _this.deleteFileSummary(fileNumLong);
              }
            }
            if (isOldVersion) {
              status=cursor.getNext(keyEntry,dataEntry,LockType.NONE,true,false);
            }
 else {
              if (!_this.getFirstFSLN(cursor,fileNum + 1,keyEntry,dataEntry,LockType.NONE)) {
                status=OperationStatus.NOTFOUND;
              }
            }
          }
        }
      }
  finally {
        if (cursor != null) {
          this.hook185();
          cursor.close();
        }
        if (locker != null) {
          locker.operationEnd();
        }
        this.hook195();
      }
      _this.cachePopulated=true;
      return true;
    }
    protected UtilizationProfile _this;
    protected int oldMemorySize;
    protected Long[] existingFiles;
    protected Locker locker;
    protected CursorImpl cursor;
    protected DatabaseEntry keyEntry;
    protected DatabaseEntry dataEntry;
    protected OperationStatus status;
    protected FileSummaryLN ln;
    protected byte[] keyBytes;
    protected boolean isOldVersion;
    protected long fileNum;
    protected Long fileNumLong;
    protected int newMemorySize;
    protected MemoryBudget mb;
    protected void hook176() throws DatabaseException {
    }
    protected void hook181() throws DatabaseException {
    }
    protected void hook182() throws DatabaseException {
    }
    protected void hook183() throws DatabaseException {
    }
    protected void hook184() throws DatabaseException {
    }
    protected void hook185() throws DatabaseException {
    }
    protected void hook191() throws DatabaseException {
    }
    protected void hook194() throws DatabaseException {
    }
    protected void hook195() throws DatabaseException {
    }
  }
  protected void hook173() throws DatabaseException {
  }
  protected void hook174() throws DatabaseException {
  }
  protected void hook175() throws DatabaseException {
  }
  protected void hook177(  long fileNum,  int sequence,  OperationStatus status) throws DatabaseException {
  }
  protected void hook178(  CursorImpl cursor) throws DatabaseException {
  }
  protected void hook179(  CursorImpl cursor) throws DatabaseException {
  }
  protected void hook180(  long lsn,  LNLogEntry entry,  DatabaseImpl db,  BIN bin) throws DatabaseException {
    Tree tree=db.getTree();
    TreeLocation location=new TreeLocation();
    boolean parentFound=tree.getParentBINForChildLN(location,entry.getKey(),entry.getDupKey(),entry.getLN(),false,true,false,false);
    bin=location.bin;
    int index=location.index;
    if (!parentFound) {
      throw new ReturnBoolean(true);
    }
    if (bin.isEntryKnownDeleted(index)) {
      throw new ReturnBoolean(true);
    }
    if (bin.getLsn(index) != lsn) {
      throw new ReturnBoolean(true);
    }
    System.err.println("lsn " + DbLsn.getNoFormatString(lsn) + " was found in tree.");
    throw new ReturnBoolean(false);
  }
  protected boolean hook186(  DatabaseImpl db,  boolean b) throws DatabaseException {
    return b;
  }
  protected void hook187(  CursorImpl cursor) throws DatabaseException {
  }
  protected void hook188(  CursorImpl cursor) throws DatabaseException {
  }
  protected void hook189(  CursorImpl cursor) throws DatabaseException {
  }
  protected void hook190(  CursorImpl cursor) throws DatabaseException {
  }
}
