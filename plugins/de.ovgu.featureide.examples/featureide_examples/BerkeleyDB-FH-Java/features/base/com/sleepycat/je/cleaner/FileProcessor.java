package com.sleepycat.je.cleaner;
import java.io.IOException;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;
import java.util.SortedMap;
import java.util.TreeMap;
import java.util.logging.Level;
import com.sleepycat.je.DatabaseException;
import com.sleepycat.je.dbi.DatabaseId;
import com.sleepycat.je.dbi.DatabaseImpl;
import com.sleepycat.je.dbi.DbTree;
import com.sleepycat.je.dbi.EnvironmentImpl;
import com.sleepycat.je.dbi.MemoryBudget;
import com.sleepycat.je.log.CleanerFileReader;
import com.sleepycat.je.tree.BIN;
import com.sleepycat.je.tree.ChildReference;
import com.sleepycat.je.tree.DIN;
import com.sleepycat.je.tree.IN;
import com.sleepycat.je.tree.LN;
import com.sleepycat.je.tree.SearchResult;
import com.sleepycat.je.tree.Tree;
import com.sleepycat.je.tree.TreeLocation;
import com.sleepycat.je.tree.WithRootLatched;
import com.sleepycat.je.txn.BasicLocker;
import com.sleepycat.je.txn.LockGrantType;
import com.sleepycat.je.txn.LockResult;
import com.sleepycat.je.txn.LockType;
import com.sleepycat.je.utilint.DaemonThread;
import com.sleepycat.je.utilint.DbLsn;
import com.sleepycat.je.utilint.Tracer;
import de.ovgu.cide.jakutil.*;
/** 
 * Reads all entries in a log file and either determines them to be obsolete or
 * marks them for migration. LNs are marked for migration by setting the BIN
 * entry MIGRATE flag. INs are marked for migration by setting the dirty flag.
 * May be invoked explicitly by calling doClean, or woken up if used as a daemon
 * thread.
 */
class FileProcessor extends DaemonThread {
  /** 
 * The number of LN log entries after we process pending LNs. If we do this
 * too seldom, the pending LN queue may grow large, and it isn't budgeted
 * memory. If we process it too often, we will repeatedly request a
 * non-blocking lock for the same locked node.
 */
  private static final int PROCESS_PENDING_EVERY_N_LNS=100;
  /** 
 * Whether to prohibit BINDeltas for a BIN that is fetched by the cleaner.
 * The theory is that when fetching a BIN during cleaning we normally expect
 * that the BIN will be evicted soon, and a delta during checkpoint would be
 * wasted. However, this does not take into account use of the BIN by the
 * application after fetching; the BIN could become hot and then deltas may
 * be profitable. To be safe we currently allow deltas when fetching.
 */
  private static final boolean PROHIBIT_DELTAS_WHEN_FETCHING=false;
  private static final boolean DEBUG_TRACING=false;
  private EnvironmentImpl env;
  private Cleaner cleaner;
  private FileSelector fileSelector;
  private UtilizationProfile profile;
  FileProcessor(  String name,  EnvironmentImpl env,  Cleaner cleaner,  UtilizationProfile profile,  FileSelector fileSelector){
    super(0,name,env);
    this.env=env;
    this.cleaner=cleaner;
    this.fileSelector=fileSelector;
    this.profile=profile;
  }
  public void clearEnv(){
    env=null;
    cleaner=null;
    fileSelector=null;
    profile=null;
  }
  /** 
 * Return the number of retries when a deadlock exception occurs.
 */
  protected int nDeadlockRetries() throws DatabaseException {
    return cleaner.nDeadlockRetries;
  }
  /** 
 * Cleaner doesn't have a work queue so just throw an exception if it's ever
 * called.
 */
  public void addToQueue(  Object o) throws DatabaseException {
    throw new DatabaseException("Cleaner.addToQueue should never be called.");
  }
  /** 
 * Activates the cleaner. Is normally called when je.cleaner.byteInterval
 * bytes are written to the log.
 */
  public void onWakeup() throws DatabaseException {
    doClean(true,true,false);
  }
  /** 
 * Cleans selected files and returns the number of files cleaned. May be
 * called by the daemon thread or programatically.
 * @param invokedFromDaemoncurrently has no effect.
 * @param cleanMultipleFilesis true to clean until we're under budget, or false to clean
 * at most one file.
 * @param forceCleaningis true to clean even if we're not under the utilization
 * threshold.
 * @return the number of files cleaned, not including files cleaned
 * unsuccessfully.
 */
  public synchronized int doClean(  boolean invokedFromDaemon,  boolean cleanMultipleFiles,  boolean forceCleaning) throws DatabaseException {
    if (env.isClosed()) {
      return 0;
    }
    int nOriginalLogFiles=profile.getNumberOfFiles();
    int nFilesCleaned=0;
    while (true) {
      if (nFilesCleaned >= nOriginalLogFiles) {
        break;
      }
      if (env.isClosing()) {
        break;
      }
      cleaner.processPending();
      cleaner.deleteSafeToDeleteFiles();
      boolean needLowUtilizationSet=cleaner.clusterResident || cleaner.clusterAll;
      Long fileNum=fileSelector.selectFileForCleaning(profile,forceCleaning,needLowUtilizationSet,cleaner.maxBatchFiles);
      cleaner.updateReadOnlyFileCollections();
      if (fileNum == null) {
        break;
      }
      this.hook138();
      boolean finished=false;
      long fileNumValue=fileNum.longValue();
      int runId=++cleaner.nCleanerRuns;
      try {
        String traceMsg="CleanerRun " + runId + " on file 0x"+ Long.toHexString(fileNumValue);
        traceMsg=this.hook139(traceMsg);
        this.hook121(traceMsg);
        if (DEBUG_TRACING) {
          System.out.println("\n" + traceMsg);
        }
        if (processFile(fileNum)) {
          fileSelector.addCleanedFile(fileNum);
          nFilesCleaned+=1;
          this.hook140();
          finished=true;
        }
      }
 catch (      IOException IOE) {
        this.hook122(IOE);
        throw new DatabaseException(IOE);
      }
 finally {
        if (!finished) {
          fileSelector.putBackFileForCleaning(fileNum);
        }
        String traceMsg="CleanerRun " + runId + " on file 0x"+ Long.toHexString(fileNumValue)+ " invokedFromDaemon="+ invokedFromDaemon+ " finished="+ finished;
        traceMsg=this.hook141(traceMsg);
        this.hook123(traceMsg);
        if (DEBUG_TRACING) {
          System.out.println("\n" + traceMsg);
        }
      }
      if (!cleanMultipleFiles) {
        break;
      }
    }
    return nFilesCleaned;
  }
  /** 
 * Process all log entries in the given file.
 * Note that we check for obsolete entries using the active TFS
 * (TrackedFileSummary) for a file while it is being processed, and we
 * prohibit flushing (eviction) of that offset information until file
 * processing is complete. An entry could become obsolete because: 1- normal
 * application activity deletes or updates the entry, 2- proactive migration
 * migrates the entry before we process it, or 3- if trackDetail is false.
 * However, checking the TFS is expensive if it has many entries, because we
 * perform a linear search. There is a tradeoff between the cost of the TFS
 * lookup and its benefit, which is to avoid a tree search if the entry is
 * obsolete. Note that many more lookups for non-obsolete entries than
 * obsolete entries will typically be done. In spite of that we check the
 * tracked summary to avoid the situation where eviction does proactive
 * migration, and evicts a BIN that is very soon afterward fetched during
 * cleaning.
 * @return false if we aborted file processing because the environment is
 * being closed.
 */
  private boolean processFile(  Long fileNum) throws DatabaseException, IOException {
    return new FileProcessor_processFile(this,fileNum).execute();
  }
  /** 
 * Processes the first LN in the look ahead cache and removes it from the
 * cache. While the BIN is latched, look through the BIN for other LNs in
 * the cache; if any match, process them to avoid a tree search later.
 * @param info
 * @param offset
 */
  private void processLN(  Long fileNum,  TreeLocation location,  Long offset,  LNInfo info,  Object lookAheadCachep,  Map dbCache) throws DatabaseException {
    new FileProcessor_processLN(this,fileNum,location,offset,info,lookAheadCachep,dbCache).execute();
  }
  /** 
 * Processes an LN that was found in the tree. Lock the LN's node ID and
 * then set the entry's MIGRATE flag if the LSN of the LN log entry is the
 * active LSN in the tree.
 * @param infoidentifies the LN log entry.
 * @param logLsnis the LSN of the log entry.
 * @param treeLsnis the LSN found in the tree.
 * @param binis the BIN found in the tree; is latched on method entry and
 * exit.
 * @param indexis the BIN index found in the tree.
 * @param parentDINis non-null for a DupCountLN only; if non-null, is latched on
 * method entry and exit.
 */
  private void processFoundLN(  LNInfo info,  long logLsn,  long treeLsn,  BIN bin,  int index,  DIN parentDIN) throws DatabaseException {
    LN ln=info.getLN();
    byte[] key=info.getKey();
    byte[] dupKey=info.getDupKey();
    DatabaseImpl db=bin.getDatabase();
    boolean isDupCountLN=parentDIN != null;
    boolean obsolete=false;
    boolean migrated=false;
    boolean lockDenied=false;
    boolean completed=false;
    long nodeId=ln.getNodeId();
    BasicLocker locker=null;
    try {
      Tree tree=db.getTree();
      assert tree != null;
      if (treeLsn != logLsn) {
        locker=new BasicLocker(env);
        LockResult lockRet=locker.nonBlockingLock(nodeId,LockType.READ,db);
        if (lockRet.getLockGrant() == LockGrantType.DENIED) {
          this.hook142();
          lockDenied=true;
        }
 else {
          this.hook143();
          obsolete=true;
        }
      }
      if (!obsolete && !lockDenied) {
        if (isDupCountLN) {
          ChildReference dclRef=parentDIN.getDupCountLNRef();
          dclRef.setMigrate(true);
          parentDIN.setDirty(true);
          if (treeLsn == logLsn && dclRef.getTarget() == null) {
            ln.postFetchInit(db,logLsn);
            parentDIN.updateDupCountLN(ln);
          }
        }
 else {
          bin.setMigrate(index,true);
          bin.setDirty(true);
          if (treeLsn == logLsn && bin.getTarget(index) == null) {
            ln.postFetchInit(db,logLsn);
            bin.updateEntry(index,ln);
          }
          if (PROHIBIT_DELTAS_WHEN_FETCHING && bin.getGeneration() == 0) {
            bin.setProhibitNextDelta();
          }
          bin.setGeneration();
        }
        this.hook144();
        migrated=true;
      }
      completed=true;
    }
  finally {
      if (locker != null) {
        locker.operationEnd();
      }
      if (completed && lockDenied) {
        fileSelector.addPendingLN(ln,db.getId(),key,dupKey);
      }
      this.hook124(logLsn,ln,obsolete,migrated,completed);
    }
  }
  /** 
 * If an IN is still in use in the in-memory tree, dirty it. The checkpoint
 * invoked at the end of the cleaning run will end up rewriting it.
 */
  private void processIN(  IN inClone,  DatabaseImpl db,  long lsn) throws DatabaseException {
    try {
      boolean obsolete=false;
      boolean dirtied=false;
      boolean completed=false;
      this.hook125(inClone,db,lsn,obsolete,dirtied,completed);
    }
 catch (    ReturnVoid r) {
      return;
    }
  }
  /** 
 * Given a clone of an IN that has been taken out of the log, try to find it
 * in the tree and verify that it is the current one in the log. Returns the
 * node in the tree if it is found and it is current re: LSN's. Otherwise
 * returns null if the clone is not found in the tree or it's not the latest
 * version. Caller is responsible for unlatching the returned IN.
 */
  private IN findINInTree(  Tree tree,  DatabaseImpl db,  IN inClone,  long lsn) throws DatabaseException {
    try {
      if (inClone.isDbRoot()) {
        IN rootIN=isRoot(tree,db,inClone,lsn);
        if (rootIN == null) {
          return null;
        }
 else {
          return rootIN;
        }
      }
      inClone.latch(Cleaner.UPDATE_GENERATION);
      SearchResult result=null;
      this.hook134(tree,db,inClone,lsn,result);
      throw ReturnHack.returnObject;
    }
 catch (    ReturnObject r) {
      return (IN)r.value;
    }
  }
private static class RootDoWork implements WithRootLatched {
    private DatabaseImpl db;
    private IN inClone;
    private long lsn;
    RootDoWork(    DatabaseImpl db,    IN inClone,    long lsn){
      this.db=db;
      this.inClone=inClone;
      this.lsn=lsn;
    }
    public IN doWork(    ChildReference root) throws DatabaseException {
      if (root == null || root.fetchTarget(db,null).getNodeId() != inClone.getNodeId()) {
        return null;
      }
      if (DbLsn.compareTo(root.getLsn(),lsn) <= 0) {
        IN rootIN=(IN)root.fetchTarget(db,null);
        rootIN.latch(Cleaner.UPDATE_GENERATION);
        return rootIN;
      }
 else {
        return null;
      }
    }
  }
  /** 
 * Check if the cloned IN is the same node as the root in tree. Return the
 * real root if it is, null otherwise. If non-null is returned, the returned
 * IN (the root) is latched -- caller is responsible for unlatching it.
 */
  private IN isRoot(  Tree tree,  DatabaseImpl db,  IN inClone,  long lsn) throws DatabaseException {
    RootDoWork rdw=new RootDoWork(db,inClone,lsn);
    return tree.withRootLatchedShared(rdw);
  }
  /** 
 * XXX: Was this intended to override Thread.toString()? If so it no longer
 * does, because we separated Thread from DaemonThread.
 */
  public String toString(){
    StringBuffer sb=new StringBuffer();
    sb.append("<Cleaner name=\"").append(name).append("\"/>");
    return sb.toString();
  }
@MethodObject static class FileProcessor_processFile {
    FileProcessor_processFile(    FileProcessor _this,    Long fileNum){
      this._this=_this;
      this.fileNum=fileNum;
    }
    boolean execute() throws DatabaseException, IOException {
      obsoleteOffsets=new PackedOffsets();
      tfs=_this.profile.getObsoleteDetail(fileNum,obsoleteOffsets,true);
      obsoleteIter=obsoleteOffsets.iterator();
      nextObsolete=-1;
      readBufferSize=_this.cleaner.readBufferSize;
      this.hook128();
      this.hook161();
      this.hook119();
      this.hook127();
      this.hook154();
      dbCache=new HashMap();
      try {
        reader=new CleanerFileReader(_this.env,readBufferSize,DbLsn.NULL_LSN,fileNum);
        this.hook137();
        dbMapTree=_this.env.getDbMapTree();
        location=new TreeLocation();
        nProcessedLNs=0;
        while (reader.readNextEntry()) {
          this.hook146();
          lsn=reader.getLastLsn();
          fileOffset=DbLsn.getFileOffset(lsn);
          isLN=reader.isLN();
          isIN=reader.isIN();
          isRoot=reader.isRoot();
          isObsolete=false;
          if (_this.env.isClosing()) {
            return false;
          }
          while (nextObsolete < fileOffset && obsoleteIter.hasNext()) {
            nextObsolete=obsoleteIter.next();
          }
          if (nextObsolete == fileOffset) {
            isObsolete=true;
          }
          if (!isObsolete && !isLN && !isIN&& !isRoot) {
            isObsolete=true;
          }
          if (!isObsolete && isLN && reader.getLN().isDeleted()) {
            isObsolete=true;
          }
          if (!isObsolete && tfs != null && tfs.containsObsoleteOffset(fileOffset)) {
            isObsolete=true;
          }
          if (isObsolete) {
            this.hook147();
            this.hook156();
            continue;
          }
          this.hook120();
          if (isLN) {
            targetLN=reader.getLN();
            dbId2=reader.getDatabaseId();
            key=reader.getKey();
            dupKey=reader.getDupTreeKey();
            aLsn=new Long(DbLsn.getFileOffset(lsn));
            aLninfo=new LNInfo(targetLN,dbId2,key,dupKey);
            this.hook130();
            nProcessedLNs+=1;
            if (nProcessedLNs % _this.PROCESS_PENDING_EVERY_N_LNS == 0) {
              _this.cleaner.processPending();
            }
          }
 else           if (isIN) {
            targetIN=reader.getIN();
            dbId3=reader.getDatabaseId();
            db3=dbMapTree.getDb(dbId3,_this.cleaner.lockTimeout,dbCache);
            targetIN.setDatabase(db3);
            _this.processIN(targetIN,db3,lsn);
          }
 else           if (isRoot) {
            _this.env.rewriteMapTreeRoot(lsn);
          }
 else {
            assert false;
          }
        }
        this.hook129();
        this.hook155();
        this.hook145();
      }
  finally {
        this.hook162();
        if (tfs != null) {
          tfs.setAllowFlush(true);
        }
      }
      return true;
    }
    protected FileProcessor _this;
    protected Long fileNum;
    protected PackedOffsets obsoleteOffsets;
    protected TrackedFileSummary tfs;
    protected PackedOffsets.Iterator obsoleteIter;
    protected long nextObsolete;
    protected int readBufferSize;
    protected int lookAheadCacheSize;
    protected int adjustMem;
    protected MemoryBudget budget;
    protected Set checkPendingDbSet;
    protected Map dbCache;
    protected CleanerFileReader reader;
    protected DbTree dbMapTree;
    protected TreeLocation location;
    protected int nProcessedLNs;
    protected long lsn;
    protected long fileOffset;
    protected boolean isLN;
    protected boolean isIN;
    protected boolean isRoot;
    protected boolean isObsolete;
    protected DatabaseId dbId1;
    protected LN targetLN;
    protected DatabaseId dbId2;
    protected byte[] key;
    protected byte[] dupKey;
    protected Long aLsn;
    protected LNInfo aLninfo;
    protected Object p;
    protected IN targetIN;
    protected DatabaseId dbId3;
    protected DatabaseImpl db3;
    protected DatabaseId dbId;
    protected DatabaseImpl db;
    protected void hook119() throws DatabaseException, IOException {
    }
    protected void hook120() throws DatabaseException, IOException {
    }
    protected void hook127() throws DatabaseException, IOException {
    }
    protected void hook128() throws DatabaseException, IOException {
    }
    protected void hook129() throws DatabaseException, IOException {
    }
    protected void hook130() throws DatabaseException, IOException {
      p=null;
      this.hook131();
      _this.processLN(fileNum,location,aLsn,aLninfo,p,dbCache);
    }
    protected void hook131() throws DatabaseException, IOException {
    }
    protected void hook137() throws DatabaseException, IOException {
    }
    protected void hook145() throws DatabaseException, IOException {
    }
    protected void hook146() throws DatabaseException, IOException {
    }
    protected void hook147() throws DatabaseException, IOException {
    }
    protected void hook154() throws DatabaseException, IOException {
    }
    protected void hook155() throws DatabaseException, IOException {
    }
    protected void hook156() throws DatabaseException, IOException {
    }
    protected void hook161() throws DatabaseException, IOException {
    }
    protected void hook162() throws DatabaseException, IOException {
    }
  }
@MethodObject static class FileProcessor_processLN {
    FileProcessor_processLN(    FileProcessor _this,    Long fileNum,    TreeLocation location,    Long offset,    LNInfo info,    Object lookAheadCachep,    Map dbCache){
      this._this=_this;
      this.fileNum=fileNum;
      this.location=location;
      this.offset=offset;
      this.info=info;
      this.lookAheadCachep=lookAheadCachep;
      this.dbCache=dbCache;
    }
    void execute() throws DatabaseException {
      this.hook132();
      ln=info.getLN();
      key=info.getKey();
      dupKey=info.getDupKey();
      logLsn=DbLsn.makeLsn(fileNum.longValue(),offset.longValue());
      db=_this.env.getDbMapTree().getDb(info.getDbId(),_this.cleaner.lockTimeout,dbCache);
      processedHere=true;
      obsolete=false;
      completed=false;
      bin=null;
      parentDIN=null;
      try {
        b=db == null;
        this.hook157();
        if (b) {
          this.hook158();
          this.hook148();
          obsolete=true;
          completed=true;
          return;
        }
        tree=db.getTree();
        assert tree != null;
        parentFound=tree.getParentBINForChildLN(location,key,dupKey,ln,false,true,false,Cleaner.UPDATE_GENERATION);
        bin=location.bin;
        index=location.index;
        if (!parentFound) {
          this.hook149();
          obsolete=true;
          completed=true;
          return;
        }
        if (bin.isEntryKnownDeleted(index)) {
          this.hook150();
          obsolete=true;
          completed=true;
          return;
        }
        isDupCountLN=ln.containsDuplicates();
{
        }
        if (isDupCountLN) {
          parentDIN=(DIN)bin.fetchTarget(index);
          parentDIN.latch(Cleaner.UPDATE_GENERATION);
          dclRef=parentDIN.getDupCountLNRef();
          treeLsn=dclRef.getLsn();
        }
 else {
          treeLsn=bin.getLsn(index);
        }
        processedHere=false;
        _this.processFoundLN(info,logLsn,treeLsn,bin,index,parentDIN);
        completed=true;
        this.hook133();
        return;
      }
  finally {
        this.hook135();
        this.hook126();
      }
    }
    protected FileProcessor _this;
    protected Long fileNum;
    protected TreeLocation location;
    protected Long offset;
    protected LNInfo info;
    protected Object lookAheadCachep;
    protected Map dbCache;
    protected LN ln;
    protected byte[] key;
    protected byte[] dupKey;
    protected long logLsn;
    protected DatabaseImpl db;
    protected boolean processedHere;
    protected boolean obsolete;
    protected boolean completed;
    protected BIN bin;
    protected DIN parentDIN;
    protected boolean b;
    protected Tree tree;
    protected boolean parentFound;
    protected int index;
    protected boolean isDupCountLN;
    protected long treeLsn;
    protected ChildReference dclRef;
    protected long lsn;
    protected Long myOffset;
    protected LNInfo myInfo;
    protected void hook126() throws DatabaseException {
    }
    protected void hook132() throws DatabaseException {
    }
    protected void hook133() throws DatabaseException {
    }
    protected void hook135() throws DatabaseException {
    }
    protected void hook148() throws DatabaseException {
    }
    protected void hook149() throws DatabaseException {
    }
    protected void hook150() throws DatabaseException {
    }
    protected void hook157() throws DatabaseException {
    }
    protected void hook158() throws DatabaseException {
    }
  }
  protected void hook121(  String traceMsg) throws DatabaseException, IOException {
  }
  protected void hook122(  IOException IOE) throws DatabaseException {
  }
  protected void hook123(  String traceMsg) throws DatabaseException {
  }
  protected void hook124(  long logLsn,  LN ln,  boolean obsolete,  boolean migrated,  boolean completed) throws DatabaseException {
  }
  protected void hook125(  IN inClone,  DatabaseImpl db,  long lsn,  boolean obsolete,  boolean dirtied,  boolean completed) throws DatabaseException {
    boolean b=db == null;
    b=this.hook159(db,b);
    if (b) {
      this.hook160(db);
      this.hook151();
      obsolete=true;
      completed=true;
      throw new ReturnVoid();
    }
    Tree tree=db.getTree();
    assert tree != null;
    IN inInTree=findINInTree(tree,db,inClone,lsn);
    if (inInTree == null) {
      this.hook152();
      obsolete=true;
    }
 else {
      this.hook153();
      inInTree.setDirty(true);
      inInTree.setProhibitNextDelta();
      this.hook136(inInTree);
      dirtied=true;
    }
    completed=true;
  }
  protected void hook134(  Tree tree,  DatabaseImpl db,  IN inClone,  long lsn,  SearchResult result) throws DatabaseException {
    result=tree.getParentINForChildIN(inClone,true,Cleaner.UPDATE_GENERATION,inClone.getLevel(),null);
    if (!result.exactParentFound) {
      throw new ReturnObject(null);
    }
    int compareVal=DbLsn.compareTo(result.parent.getLsn(result.index),lsn);
    if (compareVal > 0) {
      throw new ReturnObject(null);
    }
 else {
      IN in;
      if (compareVal == 0) {
        in=(IN)result.parent.getTarget(result.index);
        if (in == null) {
          in=inClone;
          in.postFetchInit(db,lsn);
          result.parent.updateEntry(result.index,in);
        }
      }
 else {
        in=(IN)result.parent.fetchTarget(result.index);
      }
      in.latch(Cleaner.UPDATE_GENERATION);
      throw new ReturnObject(in);
    }
  }
  protected void hook136(  IN inInTree) throws DatabaseException {
  }
  protected void hook138() throws DatabaseException {
  }
  protected String hook139(  String traceMsg) throws DatabaseException, IOException {
    return traceMsg;
  }
  protected void hook140() throws DatabaseException, IOException {
  }
  protected String hook141(  String traceMsg) throws DatabaseException {
    return traceMsg;
  }
  protected void hook142() throws DatabaseException {
  }
  protected void hook143() throws DatabaseException {
  }
  protected void hook144() throws DatabaseException {
  }
  protected void hook151() throws DatabaseException {
  }
  protected void hook152() throws DatabaseException {
  }
  protected void hook153() throws DatabaseException {
  }
  protected boolean hook159(  DatabaseImpl db,  boolean b) throws DatabaseException {
    return b;
  }
  protected void hook160(  DatabaseImpl db) throws DatabaseException {
  }
}
