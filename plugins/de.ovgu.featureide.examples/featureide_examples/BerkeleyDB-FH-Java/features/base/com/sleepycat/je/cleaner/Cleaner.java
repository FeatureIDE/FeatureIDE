package com.sleepycat.je.cleaner;
import java.io.IOException;
import java.util.Arrays;
import java.util.Collections;
import java.util.Comparator;
import java.util.Iterator;
import java.util.Set;
import java.util.logging.Level;
import java.util.logging.Logger;
import com.sleepycat.je.DatabaseException;
import com.sleepycat.je.config.EnvironmentParams;
import com.sleepycat.je.dbi.DatabaseId;
import com.sleepycat.je.dbi.DatabaseImpl;
import com.sleepycat.je.dbi.DbConfigManager;
import com.sleepycat.je.dbi.DbTree;
import com.sleepycat.je.dbi.EnvConfigObserver;
import com.sleepycat.je.dbi.EnvironmentImpl;
import com.sleepycat.je.log.FileManager;
import com.sleepycat.je.tree.BIN;
import com.sleepycat.je.tree.ChildReference;
import com.sleepycat.je.tree.DIN;
import com.sleepycat.je.tree.LN;
import com.sleepycat.je.tree.Node;
import com.sleepycat.je.tree.Tree;
import com.sleepycat.je.tree.TreeLocation;
import com.sleepycat.je.txn.BasicLocker;
import com.sleepycat.je.txn.LockGrantType;
import com.sleepycat.je.txn.LockResult;
import com.sleepycat.je.txn.LockType;
import com.sleepycat.je.utilint.DaemonRunner;
import com.sleepycat.je.utilint.DbLsn;
import com.sleepycat.je.utilint.PropUtil;
import com.sleepycat.je.utilint.Tracer;
import de.ovgu.cide.jakutil.*;
/** 
 * The Cleaner is responsible for effectively garbage collecting the JE log. It
 * looks through log files and locates log records (IN's and LN's of all
 * flavors) that are superceded by later versions. Those that are "current" are
 * propagated to a newer log file so that older log files can be deleted.
 */
public class Cleaner implements EnvConfigObserver {
  static final String CLEAN_IN="CleanIN:";
  static final String CLEAN_LN="CleanLN:";
  static final String CLEAN_MIGRATE_LN="CleanMigrateLN:";
  static final String CLEAN_PENDING_LN="CleanPendingLN:";
  /** 
 * Whether to fetch LNs for files in the to-be-cleaned set during lazy
 * migration. This is currently enabled because we do not support the
 * dynamic addition of cleaner threads; that way, if the configured cleaner
 * threads cannot keep up, we use proactive migration to keep up.
 */
  static final boolean PROACTIVE_MIGRATION=true;
  /** 
 * Whether to update the IN generation count during searches. This is
 * currently disabled because 1) we update the generation of the BIN when we
 * set a MIGRATE flag and 2) if the BIN is not evicted its parents will not
 * be, so not updating the generation during the search has no benefit. By
 * not updating the generation during searches for which we do NOT set the
 * MIGRATE flag, we avoid holding INs in the cache that are not needed for
 * lazy migration. However, we do very few searches for obsolete LNs because
 * the obsolete tracking info prevents this, so the benefit of not updating
 * the generation during searches is questionable. In other words, changing
 * this setting will have little effect.
 */
  static final boolean UPDATE_GENERATION=false;
  int nCleanerRuns=0;
  long lockTimeout;
  int readBufferSize;
  int nDeadlockRetries;
  boolean expunge;
  boolean clusterResident;
  boolean clusterAll;
  int maxBatchFiles;
  long cleanerBytesInterval;
  boolean trackDetail;
  /** 
 * All files that are to-be-cleaning or being-cleaned. Used to perform
 * proactive migration. Is read-only after assignment, so no synchronization
 * is needed.
 */
  Set mustBeCleanedFiles=Collections.EMPTY_SET;
  /** 
 * All files that are below the minUtilization threshold. Used to perform
 * clustering migration. Is read-only after assignment, so no
 * synchronization is needed.
 */
  Set lowUtilizationFiles=Collections.EMPTY_SET;
  private String name;
  private EnvironmentImpl env;
  private UtilizationProfile profile;
  private UtilizationTracker tracker;
  private FileSelector fileSelector;
  private FileProcessor[] threads;
  private Object deleteFileLock;
  public Cleaner(  EnvironmentImpl env,  String name) throws DatabaseException {
    this.env=env;
    this.name=name;
    tracker=new UtilizationTracker(env,this);
    profile=new UtilizationProfile(env,tracker);
    fileSelector=new FileSelector();
    threads=new FileProcessor[0];
    deleteFileLock=new Object();
    trackDetail=env.getConfigManager().getBoolean(EnvironmentParams.CLEANER_TRACK_DETAIL);
    envConfigUpdate(env.getConfigManager());
    env.addConfigObserver(this);
  }
  /** 
 * Process notifications of mutable property changes.
 */
  public void envConfigUpdate(  DbConfigManager cm) throws DatabaseException {
    lockTimeout=PropUtil.microsToMillis(cm.getLong(EnvironmentParams.CLEANER_LOCK_TIMEOUT));
    readBufferSize=cm.getInt(EnvironmentParams.CLEANER_READ_SIZE);
    if (readBufferSize <= 0) {
      readBufferSize=cm.getInt(EnvironmentParams.LOG_ITERATOR_READ_SIZE);
    }
    this.hook94(cm);
    nDeadlockRetries=cm.getInt(EnvironmentParams.CLEANER_DEADLOCK_RETRY);
    expunge=cm.getBoolean(EnvironmentParams.CLEANER_REMOVE);
    clusterResident=cm.getBoolean(EnvironmentParams.CLEANER_CLUSTER);
    clusterAll=cm.getBoolean(EnvironmentParams.CLEANER_CLUSTER_ALL);
    maxBatchFiles=cm.getInt(EnvironmentParams.CLEANER_MAX_BATCH_FILES);
    this.hook90();
    if (clusterResident && clusterAll) {
      throw new IllegalArgumentException("Both " + EnvironmentParams.CLEANER_CLUSTER + " and "+ EnvironmentParams.CLEANER_CLUSTER_ALL+ " may not be set to true.");
    }
    int nThreads=cm.getInt(EnvironmentParams.CLEANER_THREADS);
    assert nThreads > 0;
    if (nThreads != threads.length) {
      for (int i=nThreads; i < threads.length; i+=1) {
        if (threads[i] != null) {
          threads[i].shutdown();
          threads[i]=null;
        }
      }
      FileProcessor[] newThreads=new FileProcessor[nThreads];
      for (int i=0; i < nThreads && i < threads.length; i+=1) {
        newThreads[i]=threads[i];
      }
      threads=newThreads;
      for (int i=0; i < nThreads; i+=1) {
        if (threads[i] == null) {
          threads[i]=new FileProcessor(name + '-' + (i + 1),env,this,profile,fileSelector);
        }
      }
    }
    cleanerBytesInterval=cm.getLong(EnvironmentParams.CLEANER_BYTES_INTERVAL);
    if (cleanerBytesInterval == 0) {
      cleanerBytesInterval=cm.getLong(EnvironmentParams.LOG_FILE_MAX) / 4;
    }
  }
  public UtilizationTracker getUtilizationTracker(){
    return tracker;
  }
  public UtilizationProfile getUtilizationProfile(){
    return profile;
  }
  public void wakeup(){
    for (int i=0; i < threads.length; i+=1) {
      if (threads[i] != null) {
        threads[i].wakeup();
      }
    }
  }
  private boolean areThreadsRunning(){
    for (int i=0; i < threads.length; i+=1) {
      if (threads[i] != null) {
        return threads[i].isRunning();
      }
    }
    return false;
  }
  /** 
 * Cleans selected files and returns the number of files cleaned. This
 * method is not invoked by a deamon thread, it is programatically.
 * @param cleanMultipleFilesis true to clean until we're under budget, or false to clean
 * at most one file.
 * @param forceCleaningis true to clean even if we're not under the utilization
 * threshold.
 * @return the number of files cleaned, not including files cleaned
 * unsuccessfully.
 */
  public int doClean(  boolean cleanMultipleFiles,  boolean forceCleaning) throws DatabaseException {
    FileProcessor processor=new FileProcessor("",env,this,profile,fileSelector);
    return processor.doClean(false,cleanMultipleFiles,forceCleaning);
  }
  /** 
 * Deletes all files that are safe-to-delete, if an exclusive lock on the
 * environment can be obtained.
 */
  void deleteSafeToDeleteFiles() throws DatabaseException {
    try {
synchronized (deleteFileLock) {
        Set safeFiles=fileSelector.copySafeToDeleteFiles();
        if (safeFiles == null) {
          return;
        }
        env.checkIfInvalid();
        if (env.mayNotWrite()) {
          return;
        }
        this.hook115(safeFiles);
      }
    }
 catch (    ReturnVoid r) {
      return;
    }
  }
  private void traceFileNotDeleted(  Exception e,  long fileNum){
  }
  /** 
 * Returns a copy of the cleaned and processed files at the time a
 * checkpoint starts.
 * <p>
 * If non-null is returned, the checkpoint should flush an extra level, and
 * addCheckpointedFiles() should be called when the checkpoint is complete.
 * </p>
 */
  public Set[] getFilesAtCheckpointStart() throws DatabaseException {
    processPending();
    return fileSelector.getFilesAtCheckpointStart();
  }
  /** 
 * When a checkpoint is complete, update the files that were returned at the
 * beginning of the checkpoint.
 */
  public void updateFilesAtCheckpointEnd(  Set[] files) throws DatabaseException {
    fileSelector.updateFilesAtCheckpointEnd(files);
    deleteSafeToDeleteFiles();
  }
  /** 
 * Update the lowUtilizationFiles and mustBeCleanedFiles fields with new
 * read-only collections, and update the backlog file count.
 */
  public void updateReadOnlyFileCollections(){
    mustBeCleanedFiles=fileSelector.getMustBeCleanedFiles();
    lowUtilizationFiles=fileSelector.getLowUtilizationFiles();
  }
  /** 
 * If any LNs are pending, process them. This method should be called often
 * enough to prevent the pending LN set from growing too large.
 */
  void processPending() throws DatabaseException {
    new Cleaner_processPending(this).execute();
  }
  /** 
 * Processes a pending LN, getting the lock first to ensure that the
 * overhead of retries is mimimal.
 */
  private void processPendingLN(  LN ln,  DatabaseImpl db,  byte[] key,  byte[] dupKey,  TreeLocation location) throws DatabaseException {
    boolean parentFound=false;
    boolean processedHere=true;
    boolean lockDenied=false;
    boolean obsolete=false;
    boolean completed=false;
    BasicLocker locker=null;
    BIN bin=null;
    DIN parentDIN=null;
    try {
      this.hook97();
      boolean c=db == null;
      c=this.hook112(db,c);
      if (c) {
        this.hook113(db);
        this.hook98();
        obsolete=true;
        completed=true;
        return;
      }
      Tree tree=db.getTree();
      assert tree != null;
      locker=new BasicLocker(env);
      LockResult lockRet=locker.nonBlockingLock(ln.getNodeId(),LockType.READ,db);
      if (lockRet.getLockGrant() == LockGrantType.DENIED) {
        this.hook99();
        lockDenied=true;
        completed=true;
        return;
      }
      parentFound=tree.getParentBINForChildLN(location,key,dupKey,ln,false,true,true,UPDATE_GENERATION);
      bin=location.bin;
      int index=location.index;
      if (!parentFound) {
        this.hook100();
        obsolete=true;
        completed=true;
        return;
      }
      if (ln.containsDuplicates()) {
        parentDIN=(DIN)bin.fetchTarget(index);
        parentDIN.latch(UPDATE_GENERATION);
        ChildReference dclRef=parentDIN.getDupCountLNRef();
        processedHere=false;
        migrateDupCountLN(db,dclRef.getLsn(),parentDIN,dclRef,true,true,ln.getNodeId(),CLEAN_PENDING_LN);
      }
 else {
        processedHere=false;
        migrateLN(db,bin.getLsn(index),bin,index,true,true,ln.getNodeId(),CLEAN_PENDING_LN);
      }
      completed=true;
    }
 catch (    DatabaseException DBE) {
      DBE.printStackTrace();
      this.hook89(DBE);
      throw DBE;
    }
 finally {
      this.hook95(bin,parentDIN);
      if (locker != null) {
        locker.operationEnd();
      }
      if (processedHere) {
        if (completed && !lockDenied) {
          fileSelector.removePendingLN(ln.getNodeId());
        }
        this.hook91(ln,obsolete,completed);
      }
    }
  }
  /** 
 * This method should be called just before logging a BIN. LNs will be
 * migrated if the MIGRATE flag is set, or if they are in a file to be
 * cleaned, or if the LNs qualify according to the rules for cluster and
 * clusterAll.
 * <p>
 * On return this method guarantees that no MIGRATE flag will be set on any
 * child entry. If this method is *not* called before logging a BIN, then
 * the addPendingLNs method must be called.
 * </p>
 * @param binis the latched BIN. The latch will not be released by this
 * method.
 * @param proactiveMigrationperform proactive migration if needed; this is false during a
 * split, to reduce the delay in the user operation.
 */
  public void lazyMigrateLNs(  final BIN bin,  boolean proactiveMigration) throws DatabaseException {
    DatabaseImpl db=bin.getDatabase();
    boolean isBinInDupDb=db.getSortedDuplicates() && !bin.containsDuplicates();
    Integer[] sortedIndices=null;
    int nSortedIndices=0;
    int nEntries=bin.getNEntries();
    for (int index=0; index < nEntries; index+=1) {
      boolean migrateFlag=bin.getMigrate(index);
      boolean isResident=(bin.getTarget(index) != null);
      long childLsn=bin.getLsn(index);
      if (shouldMigrateLN(migrateFlag,isResident,proactiveMigration,isBinInDupDb,childLsn)) {
        if (isResident) {
          migrateLN(db,childLsn,bin,index,migrateFlag,false,0,CLEAN_MIGRATE_LN);
        }
 else {
          if (sortedIndices == null) {
            sortedIndices=new Integer[nEntries];
          }
          sortedIndices[nSortedIndices++]=new Integer(index);
        }
      }
    }
    if (sortedIndices != null) {
      Arrays.sort(sortedIndices,0,nSortedIndices,new Comparator(){
        public int compare(        Object o1,        Object o2){
          int i1=((Integer)o1).intValue();
          int i2=((Integer)o2).intValue();
          return DbLsn.compareTo(bin.getLsn(i1),bin.getLsn(i2));
        }
      }
);
      for (int i=0; i < nSortedIndices; i+=1) {
        int index=sortedIndices[i].intValue();
        long childLsn=bin.getLsn(index);
        boolean migrateFlag=bin.getMigrate(index);
        migrateLN(db,childLsn,bin,index,migrateFlag,false,0,CLEAN_MIGRATE_LN);
      }
    }
  }
  /** 
 * This method should be called just before logging a root DIN. The
 * DupCountLN will be migrated if the MIGRATE flag is set, or if it is in a
 * file to be cleaned, or if the LN qualifies according to the rules for
 * cluster and clusterAll.
 * <p>
 * On return this method guarantees that the MIGRATE flag will not be set on
 * the child entry. If this method is *not* called before logging a root
 * DIN, then the addPendingDupCountLN method must be called.
 * </p>
 * @param dinis the latched DIN. The latch will not be released by this
 * method.
 * @param dclRefis the reference to the DupCountLN.
 * @param proactiveMigrationperform proactive migration if needed; this is false during a
 * split, to reduce the delay in the user operation.
 */
  public void lazyMigrateDupCountLN(  DIN din,  ChildReference dclRef,  boolean proactiveMigration) throws DatabaseException {
    DatabaseImpl db=din.getDatabase();
    boolean migrateFlag=dclRef.getMigrate();
    boolean isResident=(dclRef.getTarget() != null);
    boolean isBinInDupDb=false;
    long childLsn=dclRef.getLsn();
    if (shouldMigrateLN(migrateFlag,isResident,proactiveMigration,isBinInDupDb,childLsn)) {
      migrateDupCountLN(db,childLsn,din,dclRef,migrateFlag,false,0,CLEAN_MIGRATE_LN);
    }
  }
  /** 
 * Returns whether an LN entry should be migrated. Updates stats.
 * @param migrateFlagis whether the MIGRATE flag is set on the entry.
 * @param isResidentis whether the LN is currently resident.
 * @param proactiveMigrationperform proactive migration if needed; this is false during a
 * split, to reduce the delay in the user operation.
 * @param isBinInDupDbis whether this is a BIN entry in a database with duplicates
 * enabled.
 * @param childLsnis the LSN of the LN.
 * @return whether to migrate the LN.
 */
  private boolean shouldMigrateLN(  boolean migrateFlag,  boolean isResident,  boolean proactiveMigration,  boolean isBinInDupDb,  long childLsn){
    boolean doMigration=false;
    if (migrateFlag) {
      doMigration=true;
      this.hook101();
    }
 else     if (!proactiveMigration || isBinInDupDb || env.isClosing()) {
    }
 else {
      Long fileNum=new Long(DbLsn.getFileNumber(childLsn));
      if ((PROACTIVE_MIGRATION || isResident) && mustBeCleanedFiles.contains(fileNum)) {
        doMigration=true;
        this.hook102();
      }
 else       if ((clusterAll || (clusterResident && isResident)) && lowUtilizationFiles.contains(fileNum)) {
        doMigration=true;
        this.hook103();
      }
    }
    return doMigration;
  }
  /** 
 * Migrate an LN in the given BIN entry, if it is not obsolete. The BIN is
 * latched on entry to this method and is left latched when it returns.
 */
  private void migrateLN(  DatabaseImpl db,  long lsn,  BIN bin,  int index,  boolean wasCleaned,  boolean isPending,  long lockedPendingNodeId,  String cleanAction) throws DatabaseException {
    boolean obsolete=false;
    boolean migrated=false;
    boolean lockDenied=false;
    boolean completed=false;
    boolean clearTarget=false;
    BasicLocker locker=null;
    LN ln=null;
    try {
      if (!bin.isEntryKnownDeleted(index)) {
        ln=(LN)bin.getTarget(index);
        if (ln == null) {
          ln=(LN)bin.fetchTarget(index);
          clearTarget=!db.getId().equals(DbTree.ID_DB_ID);
        }
      }
      if (ln == null) {
        this.hook105(wasCleaned);
        obsolete=true;
        completed=true;
        return;
      }
      if (lockedPendingNodeId != ln.getNodeId()) {
        locker=new BasicLocker(env);
        LockResult lockRet=locker.nonBlockingLock(ln.getNodeId(),LockType.READ,db);
        if (lockRet.getLockGrant() == LockGrantType.DENIED) {
          this.hook106(wasCleaned);
          lockDenied=true;
          completed=true;
          return;
        }
      }
      if (ln.isDeleted()) {
        bin.setKnownDeletedLeaveTarget(index);
        this.hook107(wasCleaned);
        obsolete=true;
        completed=true;
        return;
      }
      if (bin.getMigrate(index)) {
        Long fileNum=new Long(DbLsn.getFileNumber(lsn));
        if (!fileSelector.isFileCleaningInProgress(fileNum)) {
          obsolete=true;
          completed=true;
          this.hook108(wasCleaned);
          return;
        }
      }
      byte[] key=getLNMainKey(bin,index);
      long newLNLsn=ln.log(env,db.getId(),key,lsn,locker);
      bin.updateEntry(index,newLNLsn);
      this.hook104();
      migrated=true;
      completed=true;
      return;
    }
  finally {
      if (isPending) {
        if (completed && !lockDenied) {
          fileSelector.removePendingLN(lockedPendingNodeId);
        }
      }
 else {
        if (bin.getMigrate(index) && (!completed || lockDenied)) {
          byte[] key=getLNMainKey(bin,index);
          byte[] dupKey=getLNDupKey(bin,index,ln);
          fileSelector.addPendingLN(ln,db.getId(),key,dupKey);
          if (!areThreadsRunning()) {
            env.getUtilizationTracker().activateCleaner();
          }
          clearTarget=false;
        }
      }
      bin.setMigrate(index,false);
      if (clearTarget) {
        bin.updateEntry(index,null);
      }
      if (locker != null) {
        locker.operationEnd();
      }
      this.hook92(lsn,cleanAction,obsolete,migrated,completed,ln);
    }
  }
  /** 
 * Migrate the DupCountLN for the given DIN. The DIN is latched on entry to
 * this method and is left latched when it returns.
 */
  private void migrateDupCountLN(  DatabaseImpl db,  long lsn,  DIN parentDIN,  ChildReference dclRef,  boolean wasCleaned,  boolean isPending,  long lockedPendingNodeId,  String cleanAction) throws DatabaseException {
    boolean obsolete=false;
    boolean migrated=false;
    boolean lockDenied=false;
    boolean completed=false;
    boolean clearTarget=false;
    BasicLocker locker=null;
    LN ln=null;
    try {
      ln=(LN)dclRef.getTarget();
      if (ln == null) {
        ln=(LN)dclRef.fetchTarget(db,parentDIN);
        assert ln != null;
        clearTarget=!db.getId().equals(DbTree.ID_DB_ID);
      }
      if (lockedPendingNodeId != ln.getNodeId()) {
        locker=new BasicLocker(env);
        LockResult lockRet=locker.nonBlockingLock(ln.getNodeId(),LockType.READ,db);
        if (lockRet.getLockGrant() == LockGrantType.DENIED) {
          this.hook110(wasCleaned);
          lockDenied=true;
          completed=true;
          return;
        }
      }
      Long fileNum=new Long(DbLsn.getFileNumber(lsn));
      if (!fileSelector.isFileCleaningInProgress(fileNum)) {
        obsolete=true;
        completed=true;
        this.hook111(wasCleaned);
        return;
      }
      byte[] key=parentDIN.getDupKey();
      long newLNLsn=ln.log(env,db.getId(),key,lsn,locker);
      parentDIN.updateDupCountLNRef(newLNLsn);
      this.hook109();
      migrated=true;
      completed=true;
      return;
    }
  finally {
      if (isPending) {
        if (completed && !lockDenied) {
          fileSelector.removePendingLN(lockedPendingNodeId);
        }
      }
 else {
        if (dclRef.getMigrate() && (!completed || lockDenied)) {
          byte[] key=parentDIN.getDupKey();
          byte[] dupKey=null;
          fileSelector.addPendingLN(ln,db.getId(),key,dupKey);
          if (!areThreadsRunning()) {
            env.getUtilizationTracker().activateCleaner();
          }
          clearTarget=false;
        }
      }
      dclRef.setMigrate(false);
      if (clearTarget) {
        parentDIN.updateDupCountLN(null);
      }
      if (locker != null) {
        locker.operationEnd();
      }
      this.hook93(lsn,cleanAction,obsolete,migrated,completed,ln);
    }
  }
  /** 
 * Returns the main key for a given BIN entry.
 */
  private byte[] getLNMainKey(  BIN bin,  int index) throws DatabaseException {
    if (bin.containsDuplicates()) {
      return bin.getDupKey();
    }
 else {
      return bin.getKey(index);
    }
  }
  /** 
 * Returns the duplicate key for a given BIN entry.
 */
  private byte[] getLNDupKey(  BIN bin,  int index,  LN ln) throws DatabaseException {
    DatabaseImpl db=bin.getDatabase();
    if (!db.getSortedDuplicates() || ln.containsDuplicates()) {
      return null;
    }
 else     if (bin.containsDuplicates()) {
      return bin.getKey(index);
    }
 else {
      return ln.getData();
    }
  }
@MethodObject static class Cleaner_processPending {
    Cleaner_processPending(    Cleaner _this){
      this._this=_this;
    }
    void execute() throws DatabaseException {
      dbMapTree=_this.env.getDbMapTree();
      pendingLNs=_this.fileSelector.getPendingLNs();
      if (pendingLNs != null) {
        location=new TreeLocation();
        for (int i=0; i < pendingLNs.length; i+=1) {
          info=pendingLNs[i];
          dbId1=info.getDbId();
          db1=dbMapTree.getDb(dbId1,_this.lockTimeout);
          key=info.getKey();
          dupKey=info.getDupKey();
          ln=info.getLN();
          this.hook114();
          _this.processPendingLN(ln,db1,key,dupKey,location);
        }
      }
    }
    protected Cleaner _this;
    protected DbTree dbMapTree;
    protected LNInfo[] pendingLNs;
    protected TreeLocation location;
    protected LNInfo info;
    protected DatabaseId dbId1;
    protected DatabaseImpl db1;
    protected byte[] key;
    protected byte[] dupKey;
    protected LN ln;
    protected DatabaseId[] pendingDBs;
    protected DatabaseId dbId2;
    protected DatabaseImpl db2;
    protected void hook114() throws DatabaseException {
    }
  }
  protected void hook88(  long fileNumValue) throws DatabaseException {
  }
  protected void hook89(  DatabaseException DBE) throws DatabaseException {
  }
  protected void hook90() throws DatabaseException {
  }
  protected void hook91(  LN ln,  boolean obsolete,  boolean completed) throws DatabaseException {
  }
  protected void hook92(  long lsn,  String cleanAction,  boolean obsolete,  boolean migrated,  boolean completed,  LN ln) throws DatabaseException {
  }
  protected void hook93(  long lsn,  String cleanAction,  boolean obsolete,  boolean migrated,  boolean completed,  LN ln) throws DatabaseException {
  }
  protected void hook94(  DbConfigManager cm) throws DatabaseException {
  }
  protected void hook95(  BIN bin,  DIN parentDIN) throws DatabaseException {
  }
  protected void hook96() throws DatabaseException {
  }
  protected void hook97() throws DatabaseException {
  }
  protected void hook98() throws DatabaseException {
  }
  protected void hook99() throws DatabaseException {
  }
  protected void hook100() throws DatabaseException {
  }
  protected void hook101(){
  }
  protected void hook102(){
  }
  protected void hook103(){
  }
  protected void hook104() throws DatabaseException {
  }
  protected void hook105(  boolean wasCleaned) throws DatabaseException {
  }
  protected void hook106(  boolean wasCleaned) throws DatabaseException {
  }
  protected void hook107(  boolean wasCleaned) throws DatabaseException {
  }
  protected void hook108(  boolean wasCleaned) throws DatabaseException {
  }
  protected void hook109() throws DatabaseException {
  }
  protected void hook110(  boolean wasCleaned) throws DatabaseException {
  }
  protected void hook111(  boolean wasCleaned) throws DatabaseException {
  }
  protected boolean hook112(  DatabaseImpl db,  boolean c) throws DatabaseException {
    return c;
  }
  protected void hook113(  DatabaseImpl db) throws DatabaseException {
  }
  protected void hook115(  Set safeFiles) throws DatabaseException {
    for (Iterator i=safeFiles.iterator(); i.hasNext(); ) {
      Long fileNum=(Long)i.next();
      long fileNumValue=fileNum.longValue();
      boolean deleted=false;
      try {
        if (expunge) {
          env.getFileManager().deleteFile(fileNumValue);
        }
 else {
          env.getFileManager().renameFile(fileNumValue,FileManager.DEL_SUFFIX);
        }
        deleted=true;
      }
 catch (      DatabaseException e) {
        traceFileNotDeleted(e,fileNumValue);
      }
catch (      IOException e) {
        traceFileNotDeleted(e,fileNumValue);
      }
      if (deleted) {
        this.hook88(fileNumValue);
        try {
          profile.removeFile(fileNum);
        }
  finally {
          fileSelector.removeDeletedFile(fileNum);
        }
      }
      this.hook96();
    }
  }
}
