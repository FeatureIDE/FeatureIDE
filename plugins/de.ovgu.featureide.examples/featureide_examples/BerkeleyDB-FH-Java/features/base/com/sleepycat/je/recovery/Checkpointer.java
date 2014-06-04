package com.sleepycat.je.recovery;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;
import java.util.SortedMap;
import java.util.TreeMap;
import java.util.logging.Level;
import com.sleepycat.je.CheckpointConfig;
import com.sleepycat.je.DatabaseException;
import com.sleepycat.je.DbInternal;
import com.sleepycat.je.cleaner.Cleaner;
import com.sleepycat.je.cleaner.TrackedFileSummary;
import com.sleepycat.je.cleaner.UtilizationProfile;
import com.sleepycat.je.config.EnvironmentParams;
import com.sleepycat.je.dbi.DatabaseImpl;
import com.sleepycat.je.dbi.DbConfigManager;
import com.sleepycat.je.dbi.DbTree;
import com.sleepycat.je.dbi.EnvironmentImpl;
import com.sleepycat.je.dbi.INList;
import com.sleepycat.je.dbi.MemoryBudget;
import com.sleepycat.je.log.LogManager;
import com.sleepycat.je.tree.BIN;
import com.sleepycat.je.tree.IN;
import com.sleepycat.je.tree.Node;
import com.sleepycat.je.tree.SearchResult;
import com.sleepycat.je.tree.Tree;
import com.sleepycat.je.utilint.DaemonThread;
import com.sleepycat.je.utilint.DbLsn;
import com.sleepycat.je.utilint.PropUtil;
import com.sleepycat.je.utilint.Tracer;
import de.ovgu.cide.jakutil.*;
/** 
 * The Checkpointer looks through the tree for internal nodes that must be
 * flushed to the log. Checkpoint flushes must be done in ascending order from
 * the bottom of the tree up.
 */
public class Checkpointer {
  private EnvironmentImpl envImpl;
  private LogManager logManager;
  private long checkpointId;
  private long logFileMax;
  private long lastCheckpointMillis;
  private long lastFirstActiveLsn;
  private long lastCheckpointEnd;
  private volatile int highestFlushLevel;
  public Checkpointer(  EnvironmentImpl envImpl,  long waitTime,  String name) throws DatabaseException {
    this.hook538(envImpl,waitTime,name);
    this.envImpl=envImpl;
    this.hook539(envImpl);
    logFileMax=envImpl.getConfigManager().getLong(EnvironmentParams.LOG_FILE_MAX);
    this.hook531();
    this.hook545(waitTime);
    lastCheckpointMillis=0;
    highestFlushLevel=IN.MIN_LEVEL;
    logManager=envImpl.getLogManager();
  }
  public int getHighestFlushLevel(){
    return highestFlushLevel;
  }
  /** 
 * Figure out the wakeup period. Supplied through this static method because
 * we need to pass wakeup period to the superclass and need to do the
 * calcuation outside this constructor.
 */
  public static long getWakeupPeriod(  DbConfigManager configManager) throws IllegalArgumentException, DatabaseException {
    return new Checkpointer_getWakeupPeriod(configManager).execute();
  }
  /** 
 * Set checkpoint id -- can only be done after recovery.
 */
  synchronized public void setCheckpointId(  long lastCheckpointId){
    checkpointId=lastCheckpointId;
  }
  /** 
 * @return the first active LSN point of the last completed checkpoint. If
 * no checkpoint has run, return null.
 */
  public long getFirstActiveLsn(){
    return lastFirstActiveLsn;
  }
  /** 
 * Initialize the FirstActiveLsn during recovery. The cleaner needs this.
 */
  public void setFirstActiveLsn(  long lastFirstActiveLsn){
    this.lastFirstActiveLsn=lastFirstActiveLsn;
  }
  /** 
 * Determine whether a checkpoint should be run.
 * 1. If the force parameter is specified, always checkpoint.
 * 2. If the config object specifies time or log size, use that.
 * 3. If the environment is configured to use log size based checkpointing,
 * check the log.
 * 4. Lastly, use time based checking.
 */
  private boolean isRunnable(  CheckpointConfig config) throws DatabaseException {
    return new Checkpointer_isRunnable(this,config).execute();
  }
  /** 
 * The real work to do a checkpoint. This may be called by the checkpoint
 * thread when waking up, or it may be invoked programatically through the
 * api.
 * @param allowDeltasif true, this checkpoint may opt to log BIN deltas instead of
 * the full node.
 * @param flushAllif true, this checkpoint must flush all the way to the top of
 * the dbtree, instead of stopping at the highest level last
 * modified.
 * @param invokingSourcea debug aid, to indicate who invoked this checkpoint. (i.e.
 * recovery, the checkpointer daemon, the cleaner,
 * programatically)
 */
  public synchronized void doCheckpoint(  CheckpointConfig config,  boolean flushAll,  String invokingSource) throws DatabaseException {
    new Checkpointer_doCheckpoint(this,config,flushAll,invokingSource).execute();
  }
  /** 
 * Flush a FileSummaryLN node for each TrackedFileSummary that is currently
 * active. Tell the UtilizationProfile about the updated file summary.
 */
  private void flushUtilizationInfo() throws DatabaseException {
    if (!DbInternal.getCheckpointUP(envImpl.getConfigManager().getEnvironmentConfig())) {
      return;
    }
    UtilizationProfile profile=envImpl.getUtilizationProfile();
    TrackedFileSummary[] activeFiles=envImpl.getUtilizationTracker().getTrackedFiles();
    for (int i=0; i < activeFiles.length; i+=1) {
      profile.flushFileSummary(activeFiles[i]);
    }
  }
  /** 
 * Flush the nodes in order, from the lowest level to highest level. As a
 * flush dirties its parent, add it to the dirty map, thereby cascading the
 * writes up the tree. If flushAll wasn't specified, we need only cascade up
 * to the highest level set at the start of checkpointing.
 * Note that all but the top level INs and the BINDeltas are logged
 * provisionally. That's because we don't need to process lower INs because
 * the higher INs will end up pointing at them.
 */
  private void flushDirtyNodes(  SortedMap dirtyMap,  boolean flushAll,  boolean allowDeltas,  boolean flushExtraLevel,  long checkpointStart) throws DatabaseException {
    while (dirtyMap.size() > 0) {
      Integer currentLevel=(Integer)dirtyMap.firstKey();
      boolean logProvisionally=(currentLevel.intValue() != highestFlushLevel);
      Set nodeSet=(Set)dirtyMap.get(currentLevel);
      Iterator iter=nodeSet.iterator();
      while (iter.hasNext()) {
        CheckpointReference targetRef=(CheckpointReference)iter.next();
        this.hook520();
        this.hook546(dirtyMap,allowDeltas,checkpointStart,currentLevel,logProvisionally,targetRef);
        iter.remove();
      }
      dirtyMap.remove(currentLevel);
      if (currentLevel.intValue() == highestFlushLevel) {
        break;
      }
    }
  }
  /** 
 * Scan the INList for all dirty INs. Arrange them in level sorted map for
 * level ordered flushing.
 */
  private SortedMap selectDirtyINs(  boolean flushAll,  boolean flushExtraLevel) throws DatabaseException {
    return new Checkpointer_selectDirtyINs(this,flushAll,flushExtraLevel).execute();
  }
  /** 
 * Flush the target IN.
 */
  private void flushIN(  CheckpointReference targetRef,  Map dirtyMap,  int currentLevel,  boolean logProvisionally,  boolean allowDeltas,  long checkpointStart) throws DatabaseException {
    Tree tree=targetRef.db.getTree();
    boolean targetWasRoot=false;
    if (targetRef.isDbRoot) {
      RootFlusher flusher=new RootFlusher(targetRef.db,logManager,targetRef.nodeId);
      tree.withRootLatchedExclusive(flusher);
      boolean flushed=flusher.getFlushed();
      targetWasRoot=flusher.stillRoot();
      if (flushed) {
        DbTree dbTree=targetRef.db.getDbEnvironment().getDbMapTree();
        dbTree.modifyDbRoot(targetRef.db);
        this.hook532();
      }
    }
    if (!targetWasRoot) {
      SearchResult result=tree.getParentINForChildIN(targetRef.nodeId,targetRef.containsDuplicates,false,targetRef.mainTreeKey,targetRef.dupTreeKey,false,false,-1,null,false);
      if (result.parent != null) {
        boolean mustLogParent=false;
        this.hook526(targetRef,dirtyMap,currentLevel,logProvisionally,allowDeltas,checkpointStart,tree,result,mustLogParent);
      }
    }
  }
  /** 
 * @return true if this parent is appropriately 1 level above the child.
 */
  private boolean checkParentChildRelationship(  SearchResult result,  int childLevel){
    if (result.childNotResident && !result.exactParentFound) {
      return true;
    }
    int parentLevel=result.parent.getLevel();
    boolean isMapTree=(childLevel & IN.DBMAP_LEVEL) != 0;
    boolean isMainTree=(childLevel & IN.MAIN_LEVEL) != 0;
    boolean checkOk=false;
    if (isMapTree || isMainTree) {
      if (parentLevel == (childLevel + 1)) {
        checkOk=true;
      }
    }
 else {
      if (childLevel == 1) {
        if (parentLevel == 2) {
          checkOk=true;
        }
      }
 else {
        if ((parentLevel == IN.BIN_LEVEL) || (parentLevel == childLevel + 1)) {
          checkOk=true;
        }
      }
    }
    return checkOk;
  }
  private String dumpParentChildInfo(  SearchResult result,  IN parent,  long childNodeId,  int currentLevel,  Tree tree) throws DatabaseException {
    StringBuffer sb=new StringBuffer();
    sb.append("ckptId=").append(checkpointId);
    sb.append(" result=").append(result);
    sb.append(" parent node=").append(parent.getNodeId());
    sb.append(" level=").append(parent.getLevel());
    sb.append(" child node=").append(childNodeId);
    sb.append(" level=").append(currentLevel);
    return sb.toString();
  }
  private boolean logTargetAndUpdateParent(  IN target,  IN parent,  int index,  boolean allowDeltas,  long checkpointStart,  boolean logProvisionally) throws DatabaseException {
    target.latch(false);
    long newLsn=DbLsn.NULL_LSN;
    boolean mustLogParent=true;
    this.hook527(target,parent,allowDeltas,checkpointStart,logProvisionally,newLsn,mustLogParent);
    if (newLsn != DbLsn.NULL_LSN) {
      this.hook533(target);
      parent.updateEntry(index,newLsn);
    }
    return mustLogParent;
  }
  /** 
 * Add a node to the dirty map. The dirty map is keyed by level (Integers)
 * and holds sets of IN references.
 */
  private void addToDirtyMap(  Map dirtyMap,  IN in){
    Integer inLevel=new Integer(in.getLevel());
    Set inSet=(Set)dirtyMap.get(inLevel);
    if (inSet == null) {
      inSet=new HashSet();
      dirtyMap.put(inLevel,inSet);
    }
    inSet.add(new CheckpointReference(in.getDatabase(),in.getNodeId(),in.containsDuplicates(),in.isDbRoot(),in.getMainTreeKey(),in.getDupTreeKey()));
  }
public static class CheckpointReference {
    DatabaseImpl db;
    long nodeId;
    boolean containsDuplicates;
    boolean isDbRoot;
    byte[] mainTreeKey;
    byte[] dupTreeKey;
    public CheckpointReference(    DatabaseImpl db,    long nodeId,    boolean containsDuplicates,    boolean isDbRoot,    byte[] mainTreeKey,    byte[] dupTreeKey){
      this.db=db;
      this.nodeId=nodeId;
      this.containsDuplicates=containsDuplicates;
      this.isDbRoot=isDbRoot;
      this.mainTreeKey=mainTreeKey;
      this.dupTreeKey=dupTreeKey;
    }
    public boolean equals(    Object o){
      if (!(o instanceof CheckpointReference)) {
        return false;
      }
      CheckpointReference other=(CheckpointReference)o;
      return nodeId == other.nodeId;
    }
    public int hashCode(){
      return (int)nodeId;
    }
  }
@MethodObject static class Checkpointer_getWakeupPeriod {
    Checkpointer_getWakeupPeriod(    DbConfigManager configManager){
      this.configManager=configManager;
    }
    long execute() throws IllegalArgumentException, DatabaseException {
      this.hook541();
      this.hook519();
      result=0;
      this.hook540();
      return result;
    }
    protected DbConfigManager configManager;
    protected long wakeupPeriod;
    protected long bytePeriod;
    protected int result;
    protected void hook519() throws IllegalArgumentException, DatabaseException {
    }
    protected void hook540() throws IllegalArgumentException, DatabaseException {
    }
    protected void hook541() throws IllegalArgumentException, DatabaseException {
    }
  }
@MethodObject static class Checkpointer_isRunnable {
    Checkpointer_isRunnable(    Checkpointer _this,    CheckpointConfig config){
      this._this=_this;
      this.config=config;
    }
    boolean execute() throws DatabaseException {
      try {
        useBytesInterval=0;
        useTimeInterval=0;
        nextLsn=DbLsn.NULL_LSN;
        try {
          if (config.getForce()) {
            return true;
          }
 else {
            this.hook543();
          }
          this.hook542();
        }
  finally {
          this.hook521();
        }
        throw ReturnHack.returnBoolean;
      }
 catch (      ReturnBoolean r) {
        return r.value;
      }
    }
    protected Checkpointer _this;
    protected CheckpointConfig config;
    protected long useBytesInterval;
    protected long useTimeInterval;
    protected long nextLsn;
    protected long lastUsedLsn;
    protected StringBuffer sb;
    protected void hook521() throws DatabaseException {
    }
    protected void hook542() throws DatabaseException {
      throw new ReturnBoolean(false);
    }
    protected void hook543() throws DatabaseException {
      this.hook544();
    }
    protected void hook544() throws DatabaseException {
    }
  }
@MethodObject static class Checkpointer_doCheckpoint {
    Checkpointer_doCheckpoint(    Checkpointer _this,    CheckpointConfig config,    boolean flushAll,    String invokingSource){
      this._this=_this;
      this.config=config;
      this.flushAll=flushAll;
      this.invokingSource=invokingSource;
    }
    void execute() throws DatabaseException {
      if (_this.envImpl.isReadOnly()) {
        return;
      }
      if (!_this.isRunnable(config)) {
        return;
      }
      flushExtraLevel=false;
      cleaner=_this.envImpl.getCleaner();
      cleanerFiles=cleaner.getFilesAtCheckpointStart();
      if (cleanerFiles != null) {
        flushExtraLevel=true;
      }
      _this.lastCheckpointMillis=System.currentTimeMillis();
      this.hook535();
      _this.checkpointId++;
      this.hook534();
      success=false;
      this.hook522();
      this.hook548();
      mb=_this.envImpl.getMemoryBudget();
      try {
        this.hook525();
      }
  finally {
        this.hook549();
        this.hook524();
      }
    }
    protected Checkpointer _this;
    protected CheckpointConfig config;
    protected boolean flushAll;
    protected String invokingSource;
    protected boolean flushExtraLevel;
    protected Cleaner cleaner;
    protected Set[] cleanerFiles;
    protected boolean success;
    protected boolean traced;
    protected int dirtyMapMemSize;
    protected MemoryBudget mb;
    protected long checkpointStart;
    protected long firstActiveLsn;
    protected SortedMap dirtyMap;
    protected CheckpointStart startEntry;
    protected int totalSize;
    protected Set nodeSet;
    protected int size;
    protected boolean allowDeltas;
    protected CheckpointEnd endEntry;
    protected void hook522() throws DatabaseException {
    }
    protected void hook523() throws DatabaseException {
    }
    protected void hook524() throws DatabaseException {
    }
    protected void hook525() throws DatabaseException {
      checkpointStart=DbLsn.NULL_LSN;
      firstActiveLsn=DbLsn.NULL_LSN;
      dirtyMap=null;
      this.hook547();
      this.hook551();
      for (Iterator i=dirtyMap.values().iterator(); i.hasNext(); ) {
        nodeSet=(Set)i.next();
        this.hook552();
      }
      this.hook550();
      allowDeltas=!config.getMinimizeRecoveryTime();
      _this.flushDirtyNodes(dirtyMap,flushAll,allowDeltas,flushExtraLevel,checkpointStart);
      _this.flushUtilizationInfo();
      endEntry=new CheckpointEnd(invokingSource,checkpointStart,_this.envImpl.getRootLsn(),firstActiveLsn,Node.getLastId(),_this.envImpl.getDbMapTree().getLastDbId(),_this.envImpl.getTxnManager().getLastTxnId(),_this.checkpointId);
      this.hook523();
      _this.lastCheckpointEnd=_this.logManager.logForceFlush(endEntry,true);
      _this.lastFirstActiveLsn=firstActiveLsn;
      this.hook536();
      _this.highestFlushLevel=IN.MIN_LEVEL;
      success=true;
      if (cleanerFiles != null) {
        cleaner.updateFilesAtCheckpointEnd(cleanerFiles);
      }
    }
    protected void hook534() throws DatabaseException {
    }
    protected void hook535() throws DatabaseException {
    }
    protected void hook536() throws DatabaseException {
    }
    protected void hook547() throws DatabaseException {
      startEntry=new CheckpointStart(_this.checkpointId,invokingSource);
      checkpointStart=_this.logManager.log(startEntry);
      firstActiveLsn=_this.envImpl.getTxnManager().getFirstActiveLsn();
      if (firstActiveLsn == DbLsn.NULL_LSN) {
        firstActiveLsn=checkpointStart;
      }
 else {
        if (DbLsn.compareTo(checkpointStart,firstActiveLsn) < 0) {
          firstActiveLsn=checkpointStart;
        }
      }
      dirtyMap=_this.selectDirtyINs(flushAll,flushExtraLevel);
    }
    protected void hook548() throws DatabaseException {
    }
    protected void hook549() throws DatabaseException {
    }
    protected void hook550() throws DatabaseException {
    }
    protected void hook551() throws DatabaseException {
    }
    protected void hook552() throws DatabaseException {
    }
  }
@MethodObject static class Checkpointer_selectDirtyINs {
    Checkpointer_selectDirtyINs(    Checkpointer _this,    boolean flushAll,    boolean flushExtraLevel){
      this._this=_this;
      this.flushAll=flushAll;
      this.flushExtraLevel=flushExtraLevel;
    }
    SortedMap execute() throws DatabaseException {
      newDirtyMap=new TreeMap();
      inMemINs=_this.envImpl.getInMemoryINs();
      this.hook529();
      this.hook553();
      this.hook528();
      return newDirtyMap;
    }
    protected Checkpointer _this;
    protected boolean flushAll;
    protected boolean flushExtraLevel;
    protected SortedMap newDirtyMap;
    protected INList inMemINs;
    protected long totalSize;
    protected MemoryBudget mb;
    protected Iterator iter;
    protected IN in;
    protected Integer level;
    protected Set dirtySet;
    protected void hook528() throws DatabaseException {
      iter=inMemINs.iterator();
      while (iter.hasNext()) {
        in=(IN)iter.next();
        in.latch(false);
        this.hook530();
      }
      this.hook554();
      if (newDirtyMap.size() > 0) {
        if (flushAll) {
          _this.highestFlushLevel=_this.envImpl.getDbMapTree().getHighestLevel();
        }
 else {
          _this.highestFlushLevel=((Integer)newDirtyMap.lastKey()).intValue();
          if (flushExtraLevel) {
            _this.highestFlushLevel+=1;
          }
        }
      }
 else {
        _this.highestFlushLevel=IN.MAX_LEVEL;
      }
    }
    protected void hook529() throws DatabaseException {
    }
    protected void hook530() throws DatabaseException {
      if (in.getDirty()) {
        level=new Integer(in.getLevel());
{
        }
        if (newDirtyMap.containsKey(level)) {
          dirtySet=(Set)newDirtyMap.get(level);
        }
 else {
          dirtySet=new HashSet();
          newDirtyMap.put(level,dirtySet);
        }
        dirtySet.add(new CheckpointReference(in.getDatabase(),in.getNodeId(),in.containsDuplicates(),in.isDbRoot(),in.getMainTreeKey(),in.getDupTreeKey()));
      }
    }
    protected void hook553() throws DatabaseException {
    }
    protected void hook554() throws DatabaseException {
    }
  }
  protected void hook520() throws DatabaseException {
  }
  protected void hook526(  CheckpointReference targetRef,  Map dirtyMap,  int currentLevel,  boolean logProvisionally,  boolean allowDeltas,  long checkpointStart,  Tree tree,  SearchResult result,  boolean mustLogParent) throws DatabaseException {
    if (result.exactParentFound) {
      IN renewedTarget=(IN)result.parent.getTarget(result.index);
      if (renewedTarget == null) {
        mustLogParent=true;
      }
 else {
        mustLogParent=logTargetAndUpdateParent(renewedTarget,result.parent,result.index,allowDeltas,checkpointStart,logProvisionally);
      }
    }
 else {
      if (result.childNotResident) {
        if (result.parent.getLevel() > currentLevel) {
          mustLogParent=true;
        }
      }
    }
    if (mustLogParent) {
      assert checkParentChildRelationship(result,currentLevel) : dumpParentChildInfo(result,result.parent,targetRef.nodeId,currentLevel,tree);
      addToDirtyMap(dirtyMap,result.parent);
    }
  }
  protected void hook527(  IN target,  IN parent,  boolean allowDeltas,  long checkpointStart,  boolean logProvisionally,  long newLsn,  boolean mustLogParent) throws DatabaseException {
    if (target.getDirty()) {
      newLsn=target.log(logManager,allowDeltas,logProvisionally,true,parent);
      if (allowDeltas && newLsn == DbLsn.NULL_LSN) {
        this.hook537();
        long lastFullLsn=target.getLastFullVersion();
        if (DbLsn.compareTo(lastFullLsn,checkpointStart) < 0) {
          mustLogParent=false;
        }
      }
    }
  }
  protected void hook531() throws DatabaseException {
  }
  protected void hook532() throws DatabaseException {
  }
  protected void hook533(  IN target) throws DatabaseException {
  }
  protected void hook537() throws DatabaseException {
  }
  protected void hook538(  EnvironmentImpl envImpl,  long waitTime,  String name) throws DatabaseException {
  }
  protected void hook539(  EnvironmentImpl envImpl) throws DatabaseException {
  }
  protected void hook545(  long waitTime) throws DatabaseException {
  }
  protected void hook546(  SortedMap dirtyMap,  boolean allowDeltas,  long checkpointStart,  Integer currentLevel,  boolean logProvisionally,  CheckpointReference targetRef) throws DatabaseException {
  }
}
