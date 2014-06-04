package com.sleepycat.je.recovery;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.logging.Level;
import java.util.logging.Logger;
import com.sleepycat.je.CheckpointConfig;
import com.sleepycat.je.DatabaseException;
import com.sleepycat.je.DbInternal;
import com.sleepycat.je.TransactionConfig;
import com.sleepycat.je.cleaner.UtilizationTracker;
import com.sleepycat.je.config.EnvironmentParams;
import com.sleepycat.je.dbi.DatabaseId;
import com.sleepycat.je.dbi.DatabaseImpl;
import com.sleepycat.je.dbi.DbConfigManager;
import com.sleepycat.je.dbi.DbTree;
import com.sleepycat.je.dbi.EnvironmentImpl;
import com.sleepycat.je.log.CheckpointFileReader;
import com.sleepycat.je.log.FileManager;
import com.sleepycat.je.log.INFileReader;
import com.sleepycat.je.log.LNFileReader;
import com.sleepycat.je.log.LastFileReader;
import com.sleepycat.je.log.LogEntryType;
import com.sleepycat.je.tree.BIN;
import com.sleepycat.je.tree.ChildReference;
import com.sleepycat.je.tree.DIN;
import com.sleepycat.je.tree.IN;
import com.sleepycat.je.tree.Key;
import com.sleepycat.je.tree.LN;
import com.sleepycat.je.tree.Node;
import com.sleepycat.je.tree.SearchResult;
import com.sleepycat.je.tree.TrackingInfo;
import com.sleepycat.je.tree.Tree;
import com.sleepycat.je.tree.TreeLocation;
import com.sleepycat.je.tree.WithRootLatched;
import com.sleepycat.je.txn.LockType;
import com.sleepycat.je.txn.Txn;
import com.sleepycat.je.utilint.DbLsn;
import com.sleepycat.je.utilint.Tracer;
import de.ovgu.cide.jakutil.*;
public class RecoveryManager {
  private static final String TRACE_DUP_ROOT_REPLACE="DupRootRecover:";
  private static final String TRACE_LN_REDO="LNRedo:";
  private static final String TRACE_LN_UNDO="LNUndo";
  private static final String TRACE_IN_REPLACE="INRecover:";
  private static final String TRACE_ROOT_REPLACE="RootRecover:";
  private static final String TRACE_IN_DEL_REPLAY="INDelReplay:";
  private static final String TRACE_IN_DUPDEL_REPLAY="INDupDelReplay:";
  private static final String TRACE_ROOT_DELETE="RootDelete:";
  private static final int CLEAR_INCREMENT=50;
  private EnvironmentImpl env;
  private int readBufferSize;
  private RecoveryInfo info;
  private Set committedTxnIds;
  private Set abortedTxnIds;
  private Map preparedTxns;
  private Set inListRebuildDbIds;
  private Level detailedTraceLevel;
  private Map fileSummaryLsns;
  private int inListClearCounter;
  /** 
 * Make a recovery manager
 */
  public RecoveryManager(  EnvironmentImpl env) throws DatabaseException {
    this.env=env;
    DbConfigManager cm=env.getConfigManager();
    readBufferSize=cm.getInt(EnvironmentParams.LOG_ITERATOR_READ_SIZE);
    committedTxnIds=new HashSet();
    abortedTxnIds=new HashSet();
    preparedTxns=new HashMap();
    inListRebuildDbIds=new HashSet();
    fileSummaryLsns=new HashMap();
    this.hook578(env);
  }
  /** 
 * Look for an existing log and use it to create an in memory structure for
 * accessing existing databases. The file manager and logging system are
 * only available after recovery.
 * @return RecoveryInfo statistics about the recovery process.
 */
  public RecoveryInfo recover(  boolean readOnly) throws DatabaseException {
    info=new RecoveryInfo();
    try {
      FileManager fileManager=env.getFileManager();
      DbConfigManager configManager=env.getConfigManager();
      boolean forceCheckpoint=configManager.getBoolean(EnvironmentParams.ENV_RECOVERY_FORCE_CHECKPOINT);
      if (fileManager.filesExist()) {
        findEndOfLog(readOnly);
        this.hook559();
        findLastCheckpoint();
        env.getLogManager().setLastLsnAtRecovery(fileManager.getLastUsedLsn());
        this.hook558();
        env.readMapTreeFromLog(info.useRootLsn);
        buildTree();
      }
 else {
        this.hook556();
        this.hook560();
        env.logMapTreeRoot();
        forceCheckpoint=true;
      }
      if (preparedTxns.size() > 0) {
        this.hook573();
        preparedTxns=null;
      }
      if (DbInternal.getCreateUP(env.getConfigManager().getEnvironmentConfig())) {
        env.getUtilizationProfile().populateCache();
      }
      if (!readOnly && (env.getLogManager().getLastLsnAtRecovery() != info.checkpointEndLsn || forceCheckpoint)) {
        CheckpointConfig config=new CheckpointConfig();
        config.setForce(true);
        config.setMinimizeRecoveryTime(true);
        env.invokeCheckpoint(config,false,"recovery");
      }
    }
 catch (    IOException e) {
      this.hook575(e);
      throw new RecoveryException(env,"Couldn't recover: " + e.getMessage(),e);
    }
 finally {
      Tracer.trace(Level.CONFIG,env,"Recovery finished: " + info);
    }
    return info;
  }
  /** 
 * Find the end of the log, initialize the FileManager. While we're perusing
 * the log, return the last checkpoint LSN if we happen to see it.
 */
  private void findEndOfLog(  boolean readOnly) throws IOException, DatabaseException {
    LastFileReader reader=new LastFileReader(env,readBufferSize);
    while (reader.readNextEntry()) {
      LogEntryType type=reader.getEntryType();
      if (LogEntryType.LOG_CKPT_END.equals(type)) {
        info.checkpointEndLsn=reader.getLastLsn();
        info.partialCheckpointStartLsn=DbLsn.NULL_LSN;
      }
 else       if (LogEntryType.LOG_CKPT_START.equals(type)) {
        if (info.partialCheckpointStartLsn == DbLsn.NULL_LSN) {
          info.partialCheckpointStartLsn=reader.getLastLsn();
        }
      }
    }
    assert (reader.getLastValidLsn() != reader.getEndOfLog()) : "lastUsed=" + DbLsn.getNoFormatString(reader.getLastValidLsn()) + " end="+ DbLsn.getNoFormatString(reader.getEndOfLog());
    if (!readOnly) {
      reader.setEndOfFile();
    }
    info.lastUsedLsn=reader.getLastValidLsn();
    info.nextAvailableLsn=reader.getEndOfLog();
    info.nRepeatIteratorReads+=reader.getNRepeatIteratorReads();
    env.getFileManager().setLastPosition(info.nextAvailableLsn,info.lastUsedLsn,reader.getPrevOffset());
  }
  /** 
 * Find the last checkpoint and establish the firstActiveLsn point,
 * checkpoint start, and checkpoint end.
 */
  private void findLastCheckpoint() throws IOException, DatabaseException {
    if (info.checkpointEndLsn == DbLsn.NULL_LSN) {
      CheckpointFileReader searcher=new CheckpointFileReader(env,readBufferSize,false,info.lastUsedLsn,DbLsn.NULL_LSN,info.nextAvailableLsn);
      while (searcher.readNextEntry()) {
        if (searcher.isCheckpointEnd()) {
          info.checkpointEndLsn=searcher.getLastLsn();
          break;
        }
 else         if (searcher.isCheckpointStart()) {
          info.partialCheckpointStartLsn=searcher.getLastLsn();
        }
 else         if (searcher.isRoot()) {
          if (info.useRootLsn == DbLsn.NULL_LSN) {
            info.useRootLsn=searcher.getLastLsn();
          }
        }
      }
      info.nRepeatIteratorReads+=searcher.getNRepeatIteratorReads();
    }
    if (info.checkpointEndLsn == DbLsn.NULL_LSN) {
      info.checkpointStartLsn=DbLsn.NULL_LSN;
      info.firstActiveLsn=DbLsn.NULL_LSN;
    }
 else {
      CheckpointEnd checkpointEnd=(CheckpointEnd)(env.getLogManager().get(info.checkpointEndLsn));
      info.checkpointEnd=checkpointEnd;
      info.checkpointStartLsn=checkpointEnd.getCheckpointStartLsn();
      info.firstActiveLsn=checkpointEnd.getFirstActiveLsn();
      if (checkpointEnd.getRootLsn() != DbLsn.NULL_LSN) {
        info.useRootLsn=checkpointEnd.getRootLsn();
      }
      env.getCheckpointer().setCheckpointId(checkpointEnd.getId());
      env.getCheckpointer().setFirstActiveLsn(checkpointEnd.getFirstActiveLsn());
    }
    if (info.useRootLsn == DbLsn.NULL_LSN) {
      throw new RecoveryException(env,"This environment's log file has no root. Since the root " + "is the first entry written into a log at environment " + "creation, this should only happen if the initial creation "+ "of the environment was never checkpointed or synced. "+ "Please move aside the existing log files to allow the "+ "creation of a new environment");
    }
  }
  /** 
 * Use the log to recreate an in memory tree.
 */
  private void buildTree() throws IOException, DatabaseException {
    inListClearCounter=0;
    this.hook572();
    long start=System.currentTimeMillis();
    readINsAndTrackIds(info.checkpointStartLsn);
    long end=System.currentTimeMillis();
    this.hook571(start,end);
    start=System.currentTimeMillis();
    info.numOtherINs+=readINs(info.checkpointStartLsn,true,LogEntryType.LOG_BIN_DELTA,null,null,true);
    end=System.currentTimeMillis();
    this.hook570(start,end);
    start=System.currentTimeMillis();
    Set mapLNSet=new HashSet();
    mapLNSet.add(LogEntryType.LOG_MAPLN_TRANSACTIONAL);
    mapLNSet.add(LogEntryType.LOG_TXN_COMMIT);
    mapLNSet.add(LogEntryType.LOG_TXN_ABORT);
    mapLNSet.add(LogEntryType.LOG_TXN_PREPARE);
    undoLNs(info,mapLNSet);
    end=System.currentTimeMillis();
    this.hook569(start,end);
    start=System.currentTimeMillis();
    mapLNSet.add(LogEntryType.LOG_MAPLN);
    redoLNs(info,mapLNSet);
    end=System.currentTimeMillis();
    this.hook568(start,end);
    start=System.currentTimeMillis();
    info.numOtherINs+=readINs(info.checkpointStartLsn,false,LogEntryType.LOG_IN,LogEntryType.LOG_BIN,LogEntryType.LOG_IN_DELETE_INFO,false);
    end=System.currentTimeMillis();
    this.hook567(start,end);
    start=System.currentTimeMillis();
    info.numBinDeltas=readINs(info.checkpointStartLsn,false,LogEntryType.LOG_BIN_DELTA,null,null,true);
    end=System.currentTimeMillis();
    this.hook566(start,end);
    start=System.currentTimeMillis();
    info.numDuplicateINs+=readINs(info.checkpointStartLsn,false,LogEntryType.LOG_DIN,LogEntryType.LOG_DBIN,LogEntryType.LOG_IN_DUPDELETE_INFO,true);
    end=System.currentTimeMillis();
    this.hook565(start,end);
    start=System.currentTimeMillis();
    info.numBinDeltas+=readINs(info.checkpointStartLsn,false,LogEntryType.LOG_DUP_BIN_DELTA,null,null,true);
    end=System.currentTimeMillis();
    this.hook564(start,end);
    rebuildINList();
    this.hook596();
    this.hook563();
    start=System.currentTimeMillis();
    Set lnSet=new HashSet();
    lnSet.add(LogEntryType.LOG_LN_TRANSACTIONAL);
    lnSet.add(LogEntryType.LOG_NAMELN_TRANSACTIONAL);
    lnSet.add(LogEntryType.LOG_DEL_DUPLN_TRANSACTIONAL);
    lnSet.add(LogEntryType.LOG_DUPCOUNTLN_TRANSACTIONAL);
    undoLNs(info,lnSet);
    end=System.currentTimeMillis();
    this.hook562(start,end);
    start=System.currentTimeMillis();
    lnSet.add(LogEntryType.LOG_LN);
    lnSet.add(LogEntryType.LOG_NAMELN);
    lnSet.add(LogEntryType.LOG_DEL_DUPLN);
    lnSet.add(LogEntryType.LOG_DUPCOUNTLN);
    lnSet.add(LogEntryType.LOG_FILESUMMARYLN);
    redoLNs(info,lnSet);
    end=System.currentTimeMillis();
    this.hook561(start,end);
  }
  private void readINsAndTrackIds(  long rollForwardLsn) throws IOException, DatabaseException {
    INFileReader reader=new INFileReader(env,readBufferSize,rollForwardLsn,info.nextAvailableLsn,true,false,info.partialCheckpointStartLsn,fileSummaryLsns);
    reader.addTargetType(LogEntryType.LOG_IN);
    reader.addTargetType(LogEntryType.LOG_BIN);
    reader.addTargetType(LogEntryType.LOG_IN_DELETE_INFO);
    this.hook593(reader);
    try {
      info.numMapINs=0;
      DbTree dbMapTree=env.getDbMapTree();
      while (reader.readNextEntry()) {
        DatabaseId dbId=reader.getDatabaseId();
        if (dbId.equals(DbTree.ID_DB_ID)) {
          DatabaseImpl db=dbMapTree.getDb(dbId);
          replayOneIN(reader,db,false);
          info.numMapINs++;
        }
      }
      info.useMaxNodeId=reader.getMaxNodeId();
      info.useMaxDbId=reader.getMaxDbId();
      info.useMaxTxnId=reader.getMaxTxnId();
      if (info.checkpointEnd != null) {
        if (info.useMaxNodeId < info.checkpointEnd.getLastNodeId()) {
          info.useMaxNodeId=info.checkpointEnd.getLastNodeId();
        }
        if (info.useMaxDbId < info.checkpointEnd.getLastDbId()) {
          info.useMaxDbId=info.checkpointEnd.getLastDbId();
        }
        if (info.useMaxTxnId < info.checkpointEnd.getLastTxnId()) {
          info.useMaxTxnId=info.checkpointEnd.getLastTxnId();
        }
      }
      Node.setLastNodeId(info.useMaxNodeId);
      env.getDbMapTree().setLastDbId(info.useMaxDbId);
      env.getTxnManager().setLastTxnId(info.useMaxTxnId);
      info.nRepeatIteratorReads+=reader.getNRepeatIteratorReads();
    }
 catch (    Exception e) {
      traceAndThrowException(reader.getLastLsn(),"readMapIns",e);
    }
  }
  /** 
 * Read INs and process.
 */
  private int readINs(  long rollForwardLsn,  boolean mapDbOnly,  LogEntryType inType1,  LogEntryType inType2,  LogEntryType inType3,  boolean requireExactMatch) throws IOException, DatabaseException {
    INFileReader reader=new INFileReader(env,readBufferSize,rollForwardLsn,info.nextAvailableLsn,false,mapDbOnly,info.partialCheckpointStartLsn,fileSummaryLsns);
    if (inType1 != null) {
      reader.addTargetType(inType1);
    }
    if (inType2 != null) {
      reader.addTargetType(inType2);
    }
    if (inType3 != null) {
      reader.addTargetType(inType3);
    }
    int numINsSeen=0;
    try {
      DbTree dbMapTree=env.getDbMapTree();
      while (reader.readNextEntry()) {
        DatabaseId dbId=reader.getDatabaseId();
        boolean isMapDb=dbId.equals(DbTree.ID_DB_ID);
        boolean isTarget=false;
        if (mapDbOnly && isMapDb) {
          isTarget=true;
        }
 else         if (!mapDbOnly && !isMapDb) {
          isTarget=true;
        }
        if (isTarget) {
          DatabaseImpl db=dbMapTree.getDb(dbId);
          if (db == null) {
          }
 else {
            replayOneIN(reader,db,requireExactMatch);
            numINsSeen++;
            inListRebuildDbIds.add(dbId);
          }
        }
      }
      info.nRepeatIteratorReads+=reader.getNRepeatIteratorReads();
      return numINsSeen;
    }
 catch (    Exception e) {
      traceAndThrowException(reader.getLastLsn(),"readNonMapIns",e);
      return 0;
    }
  }
  /** 
 * Get an IN from the reader, set its database, and fit into tree.
 */
  private void replayOneIN(  INFileReader reader,  DatabaseImpl db,  boolean requireExactMatch) throws DatabaseException {
    if (reader.isDeleteInfo()) {
      replayINDelete(db,reader.getDeletedNodeId(),false,reader.getDeletedIdKey(),null,reader.getLastLsn());
    }
 else     if (reader.isDupDeleteInfo()) {
      replayINDelete(db,reader.getDupDeletedNodeId(),true,reader.getDupDeletedMainKey(),reader.getDupDeletedDupKey(),reader.getLastLsn());
    }
 else {
      IN in=reader.getIN();
      long inLsn=reader.getLsnOfIN();
      in.postRecoveryInit(db,inLsn);
      this.hook585(in);
      replaceOrInsert(db,in,reader.getLastLsn(),inLsn,requireExactMatch);
    }
    if ((++inListClearCounter % CLEAR_INCREMENT) == 0) {
      env.getInMemoryINs().clear();
    }
  }
  /** 
 * Undo all aborted LNs. To do so, walk the log backwards, keeping a
 * collection of committed txns. If we see a log entry that doesn't have a
 * committed txn, undo it.
 */
  private void undoLNs(  RecoveryInfo info,  Set lnTypes) throws IOException, DatabaseException {
    long firstActiveLsn=info.firstActiveLsn;
    long lastUsedLsn=info.lastUsedLsn;
    long endOfFileLsn=info.nextAvailableLsn;
    LNFileReader reader=new LNFileReader(env,readBufferSize,lastUsedLsn,false,endOfFileLsn,firstActiveLsn,null);
    Iterator iter=lnTypes.iterator();
    while (iter.hasNext()) {
      LogEntryType lnType=(LogEntryType)iter.next();
      reader.addTargetType(lnType);
    }
    Map countedFileSummaries=new HashMap();
    Set countedAbortLsnNodes=new HashSet();
    DbTree dbMapTree=env.getDbMapTree();
    TreeLocation location=new TreeLocation();
    try {
      while (reader.readNextEntry()) {
        if (reader.isLN()) {
          Long txnId=reader.getTxnId();
          if (txnId != null && !committedTxnIds.contains(txnId)) {
            this.hook597();
            LN ln=reader.getLN();
            long logLsn=reader.getLastLsn();
            long abortLsn=reader.getAbortLsn();
            boolean abortKnownDeleted=reader.getAbortKnownDeleted();
            DatabaseId dbId=reader.getDatabaseId();
            DatabaseImpl db=dbMapTree.getDb(dbId);
            if (db != null) {
              ln.postFetchInit(db,logLsn);
              this.hook586(info,reader,location,ln,logLsn,abortLsn,abortKnownDeleted,db);
              TxnNodeId txnNodeId=new TxnNodeId(reader.getNodeId(),txnId.longValue());
              undoUtilizationInfo(ln,logLsn,abortLsn,abortKnownDeleted,txnNodeId,countedFileSummaries,countedAbortLsnNodes);
              inListRebuildDbIds.add(dbId);
            }
          }
        }
 else         if (reader.isPrepare()) {
          long prepareId=reader.getTxnPrepareId();
          Long prepareIdL=new Long(prepareId);
          if (!committedTxnIds.contains(prepareIdL) && !abortedTxnIds.contains(prepareIdL)) {
            TransactionConfig txnConf=new TransactionConfig();
            Txn preparedTxn=new Txn(env,txnConf,prepareId);
            preparedTxn.setLockTimeout(0);
            preparedTxns.put(prepareIdL,preparedTxn);
            env.getTxnManager().registerXATxn(reader.getTxnPrepareXid(),preparedTxn,true);
            this.hook574(reader);
          }
        }
 else         if (reader.isAbort()) {
          abortedTxnIds.add(new Long(reader.getTxnAbortId()));
        }
 else {
          committedTxnIds.add(new Long(reader.getTxnCommitId()));
        }
      }
      info.nRepeatIteratorReads+=reader.getNRepeatIteratorReads();
    }
 catch (    Exception e) {
      traceAndThrowException(reader.getLastLsn(),"undoLNs",e);
    }
  }
  /** 
 * Apply all committed LNs.
 * @param rollForwardLsnstart redoing from this point
 * @param lnType1targetted LN
 * @param lnType2targetted LN
 */
  private void redoLNs(  RecoveryInfo info,  Set lnTypes) throws IOException, DatabaseException {
    long endOfFileLsn=info.nextAvailableLsn;
    long rollForwardLsn=info.checkpointStartLsn;
    LNFileReader reader=new LNFileReader(env,readBufferSize,rollForwardLsn,true,DbLsn.NULL_LSN,endOfFileLsn,null);
    Iterator iter=lnTypes.iterator();
    while (iter.hasNext()) {
      LogEntryType lnType=(LogEntryType)iter.next();
      reader.addTargetType(lnType);
    }
    Set countedAbortLsnNodes=new HashSet();
    DbTree dbMapTree=env.getDbMapTree();
    TreeLocation location=new TreeLocation();
    try {
      while (reader.readNextEntry()) {
        if (reader.isLN()) {
          Long txnId=reader.getTxnId();
          boolean processThisLN=false;
          boolean lnIsCommitted=false;
          boolean lnIsPrepared=false;
          Txn preparedTxn=null;
          if (txnId == null) {
            processThisLN=true;
          }
 else {
            lnIsCommitted=committedTxnIds.contains(txnId);
            if (!lnIsCommitted) {
              preparedTxn=(Txn)preparedTxns.get(txnId);
              lnIsPrepared=preparedTxn != null;
            }
            if (lnIsCommitted || lnIsPrepared) {
              processThisLN=true;
            }
          }
          if (processThisLN) {
            this.hook598();
            LN ln=reader.getLN();
            DatabaseId dbId=reader.getDatabaseId();
            DatabaseImpl db=dbMapTree.getDb(dbId);
            long logLsn=reader.getLastLsn();
            long treeLsn=DbLsn.NULL_LSN;
            if (db != null) {
              ln.postFetchInit(db,logLsn);
              if (preparedTxn != null) {
                preparedTxn.addLogInfo(logLsn);
                preparedTxn.lock(ln.getNodeId(),LockType.WRITE,false,db);
                preparedTxn.setPrepared(true);
              }
              treeLsn=redo(db,location,ln,reader.getKey(),reader.getDupTreeKey(),logLsn,info);
              inListRebuildDbIds.add(dbId);
            }
            TxnNodeId txnNodeId=null;
            if (txnId != null) {
              txnNodeId=new TxnNodeId(reader.getNodeId(),txnId.longValue());
            }
            redoUtilizationInfo(logLsn,treeLsn,reader.getAbortLsn(),reader.getAbortKnownDeleted(),ln,txnNodeId,countedAbortLsnNodes);
          }
        }
      }
      info.nRepeatIteratorReads+=reader.getNRepeatIteratorReads();
    }
 catch (    Exception e) {
      traceAndThrowException(reader.getLastLsn(),"redoLns",e);
    }
  }
  /** 
 * Rebuild the in memory inList with INs that have been made resident by the
 * recovery process.
 */
  private void rebuildINList() throws DatabaseException {
    env.getInMemoryINs().clear();
    env.getDbMapTree().rebuildINListMapDb();
    Iterator iter=inListRebuildDbIds.iterator();
    while (iter.hasNext()) {
      DatabaseId dbId=(DatabaseId)iter.next();
      if (!dbId.equals(DbTree.ID_DB_ID)) {
        DatabaseImpl db=env.getDbMapTree().getDb(dbId);
        if (db != null) {
          db.getTree().rebuildINList();
        }
      }
    }
  }
private static class TxnNodeId {
    long nodeId;
    long txnId;
    TxnNodeId(    long nodeId,    long txnId){
      this.nodeId=nodeId;
      this.txnId=txnId;
    }
    /** 
 * Compare two TxnNodeId objects
 */
    public boolean equals(    Object obj){
      if (this == obj) {
        return true;
      }
      if (!(obj instanceof TxnNodeId)) {
        return false;
      }
      return ((((TxnNodeId)obj).txnId == txnId) && (((TxnNodeId)obj).nodeId == nodeId));
    }
    public int hashCode(){
      return (int)(txnId + nodeId);
    }
    public String toString(){
      return "txnId=" + txnId + "/nodeId="+ nodeId;
    }
  }
  /** 
 * Recover an internal node. If inFromLog is: - not found, insert it in the
 * appropriate location. - if found and there is a physical match (LSNs are
 * the same) do nothing. - if found and there is a logical match (LSNs are
 * different, another version of this IN is in place, replace the found node
 * with the node read from the log only if the log version's LSN is greater.
 * InFromLog should be latched upon entering this method and it will not be
 * latched upon exiting.
 * @param inFromLog -
 * the new node to put in the tree. The identifier key and node
 * id are used to find the existing version of the node.
 * @param logLsn -
 * the location of log entry in in the log.
 * @param inLsnLSN of this in -- may not be the same as the log LSN if the
 * current entry is a BINDelta
 * @param requireExactMatch -
 * true if we won't place this node in the tree unless we find
 * exactly that parent. Used for BINDeltas, where we want to only
 * apply the BINDelta to that exact node.
 */
  private void replaceOrInsert(  DatabaseImpl db,  IN inFromLog,  long logLsn,  long inLsn,  boolean requireExactMatch) throws DatabaseException {
    List trackingList=null;
    try {
      if (inFromLog.isRoot()) {
        if (inFromLog.containsDuplicates()) {
          replaceOrInsertDuplicateRoot(db,(DIN)inFromLog,logLsn);
        }
 else {
          replaceOrInsertRoot(db,inFromLog,logLsn);
        }
      }
 else {
        trackingList=new ArrayList();
        replaceOrInsertChild(db,inFromLog,logLsn,inLsn,trackingList,requireExactMatch);
      }
    }
 catch (    Exception e) {
      String trace=printTrackList(trackingList);
      this.hook576(db,logLsn,e,trace);
      throw new DatabaseException("lsnFromLog=" + DbLsn.getNoFormatString(logLsn),e);
    }
 finally {
      this.hook587(inFromLog,logLsn);
    }
  }
  /** 
 * Dump a tracking list into a string.
 */
  private String printTrackList(  List trackingList){
    if (trackingList != null) {
      StringBuffer sb=new StringBuffer();
      Iterator iter=trackingList.iterator();
      sb.append("Trace list:");
      sb.append('\n');
      while (iter.hasNext()) {
        sb.append((TrackingInfo)iter.next());
        sb.append('\n');
      }
      return sb.toString();
    }
 else {
      return null;
    }
  }
  /** 
 * Replay an IN delete. Remove an entry from an IN to reflect a reverse
 * split.
 */
  private void replayINDelete(  DatabaseImpl db,  long nodeId,  boolean containsDuplicates,  byte[] mainKey,  byte[] dupKey,  long logLsn) throws DatabaseException {
    boolean found=false;
    boolean deleted=false;
    Tree tree=db.getTree();
    SearchResult result=new SearchResult();
    try {
      result=db.getTree().getParentINForChildIN(nodeId,containsDuplicates,false,mainKey,dupKey,false,false,-1,null,true);
      if (result.parent == null) {
        tree.withRootLatchedExclusive(new RootDeleter(tree));
        DbTree dbTree=db.getDbEnvironment().getDbMapTree();
        dbTree.modifyDbRoot(db);
        this.hook557(db);
        deleted=true;
      }
 else       if (result.exactParentFound) {
        found=true;
        deleted=result.parent.deleteEntry(result.index,false);
      }
    }
  finally {
      this.hook588(result);
      this.hook579(nodeId,containsDuplicates,logLsn,found,deleted,result);
    }
  }
private static class RootDeleter implements WithRootLatched {
    Tree tree;
    RootDeleter(    Tree tree){
      this.tree=tree;
    }
    /** 
 * @return true if the in-memory root was replaced.
 */
    public IN doWork(    ChildReference root) throws DatabaseException {
      tree.setRoot(null,false);
      return null;
    }
  }
  /** 
 * If the root of this tree is null, use this IN from the log as a root.
 * Note that we should really also check the LSN of the mapLN, because
 * perhaps the root is null because it's been deleted. However, the replay
 * of all the LNs will end up adjusting the tree correctly.
 * If there is a root, check if this IN is a different LSN and if so,
 * replace it.
 */
  private void replaceOrInsertRoot(  DatabaseImpl db,  IN inFromLog,  long lsn) throws DatabaseException {
    boolean success=true;
    Tree tree=db.getTree();
    RootUpdater rootUpdater=new RootUpdater(tree,inFromLog,lsn);
    try {
      tree.withRootLatchedExclusive(rootUpdater);
      if (rootUpdater.updateDone()) {
        EnvironmentImpl env=db.getDbEnvironment();
        env.getDbMapTree().modifyDbRoot(db);
      }
    }
 catch (    Exception e) {
      success=false;
      throw new DatabaseException("lsnFromLog=" + DbLsn.getNoFormatString(lsn),e);
    }
 finally {
      this.hook580(db,inFromLog,lsn,success,rootUpdater);
    }
  }
  /** 
 * Recover this root of a duplicate tree.
 */
  private void replaceOrInsertDuplicateRoot(  DatabaseImpl db,  DIN inFromLog,  long lsn) throws DatabaseException {
    boolean found=true;
    boolean inserted=false;
    boolean replaced=false;
    long origLsn=DbLsn.NULL_LSN;
    byte[] mainTreeKey=inFromLog.getMainTreeKey();
    IN parent=null;
    int index=-1;
    boolean success=false;
    try {
      parent=db.getTree().searchSplitsAllowed(mainTreeKey,-1,true);
      assert parent instanceof BIN;
      ChildReference newRef=new ChildReference(inFromLog,mainTreeKey,lsn);
      index=parent.insertEntry1(newRef);
      if ((index >= 0 && (index & IN.EXACT_MATCH) != 0)) {
        index&=~IN.EXACT_MATCH;
        if (parent.isEntryKnownDeleted(index)) {
          parent.setEntry(index,inFromLog,mainTreeKey,lsn,(byte)0);
          replaced=true;
        }
 else {
          origLsn=parent.getLsn(index);
          if (DbLsn.compareTo(origLsn,lsn) < 0) {
            parent.setEntry(index,inFromLog,mainTreeKey,lsn,parent.getState(index));
            replaced=true;
          }
        }
      }
 else {
        found=false;
      }
      success=true;
    }
  finally {
      this.hook589(parent);
      this.hook581(db,inFromLog,lsn,found,inserted,replaced,origLsn,parent,index,success);
    }
  }
  private void replaceOrInsertChild(  DatabaseImpl db,  IN inFromLog,  long logLsn,  long inLsn,  List trackingList,  boolean requireExactMatch) throws DatabaseException {
    boolean inserted=false;
    boolean replaced=false;
    long origLsn=DbLsn.NULL_LSN;
    boolean success=false;
    SearchResult result=new SearchResult();
    try {
      result=db.getTree().getParentINForChildIN(inFromLog,requireExactMatch,false,-1,trackingList);
      if (result.parent == null) {
        return;
      }
      if (result.index >= 0) {
        if (result.parent.getLsn(result.index) == logLsn) {
        }
 else {
          if (result.exactParentFound) {
            origLsn=result.parent.getLsn(result.index);
            if (DbLsn.compareTo(origLsn,logLsn) < 0) {
              result.parent.updateEntry(result.index,inFromLog,inLsn);
              replaced=true;
            }
          }
        }
      }
      success=true;
    }
  finally {
      this.hook590(result);
      this.hook582(db,inFromLog,logLsn,inserted,replaced,origLsn,success,result);
    }
  }
  /** 
 * Redo a committed LN for recovery.
 * <pre>
 * log LN found  | logLSN &gt; LSN | LN is deleted | action
 * in tree     | in tree      |               |
 * --------------+--------------+---------------+------------------------
 * Y         |    N         |    n/a        | no action
 * --------------+--------------+---------------+------------------------
 * Y         |    Y         |     N         | replace w/log LSN
 * --------------+--------------+---------------+------------------------
 * Y         |    Y         |     Y         | replace w/log LSN, put
 * |              |               | on compressor queue
 * --------------+--------------+---------------+------------------------
 * N         |    n/a       |     N         | insert into tree
 * --------------+--------------+---------------+------------------------
 * N         |    n/a       |     Y         | no action
 * --------------+--------------+---------------+------------------------
 * </pre>
 * @param locationholds state about the search in the tree. Passed in from the
 * recovery manager to reduce objection creation overhead.
 * @param lnFromLog -
 * the new node to put in the tree.
 * @param mainKeyis the key that navigates us through the main tree
 * @param dupTreeKeyis the key that navigates us through the duplicate tree
 * @param logLsnis the LSN from the just-read log entry
 * @param infois a recovery stats object.
 * @return the LSN found in the tree, or null if not found.
 */
  private long redo(  DatabaseImpl db,  TreeLocation location,  LN lnFromLog,  byte[] mainKey,  byte[] dupKey,  long logLsn,  RecoveryInfo info) throws DatabaseException {
    boolean found=false;
    boolean replaced=false;
    boolean inserted=false;
    boolean success=false;
    try {
      location.reset();
      found=db.getTree().getParentBINForChildLN(location,mainKey,dupKey,lnFromLog,true,false,true,true);
      if (!found && (location.bin == null)) {
        success=true;
        return DbLsn.NULL_LSN;
      }
      if (lnFromLog.containsDuplicates()) {
        if (found) {
          DIN duplicateRoot=(DIN)location.bin.fetchTarget(location.index);
          if (DbLsn.compareTo(logLsn,location.childLsn) >= 0) {
            duplicateRoot.updateDupCountLNRefAndNullTarget(logLsn);
          }
        }
      }
 else {
        if (found) {
          info.lnFound++;
          if (DbLsn.compareTo(logLsn,location.childLsn) > 0) {
            info.lnReplaced++;
            replaced=true;
            location.bin.updateEntry(location.index,null,logLsn);
          }
          if (DbLsn.compareTo(logLsn,location.childLsn) >= 0 && lnFromLog.isDeleted()) {
            location.bin.setKnownDeletedLeaveTarget(location.index);
            byte[] deletedKey=location.bin.containsDuplicates() ? dupKey : mainKey;
            this.hook594(db,location,deletedKey);
          }
        }
 else {
          info.lnNotFound++;
          if (!lnFromLog.isDeleted()) {
            info.lnInserted++;
            inserted=true;
            boolean insertOk=insertRecovery(db,location,logLsn);
            assert insertOk;
          }
        }
      }
      success=true;
      return found ? location.childLsn : DbLsn.NULL_LSN;
    }
  finally {
      this.hook591(location);
      this.hook583(db,location,lnFromLog,logLsn,found,replaced,inserted,success);
    }
  }
  /** 
 * Undo the changes to this node. Here are the rules that govern the action
 * taken.
 * <pre>
 * found LN in  | abortLsn is | logLsn ==       | action taken
 * tree      | null        | LSN in tree     | by undo
 * -------------+-------------+----------------------------------------
 * Y       |     N       |      Y          | replace w/abort LSN
 * ------------ +-------------+-----------------+-----------------------
 * Y       |     Y       |      Y          | remove from tree
 * ------------ +-------------+-----------------+-----------------------
 * Y       |     N/A     |      N          | no action
 * ------------ +-------------+-----------------+-----------------------
 * N       |     N/A     |    N/A          | no action (*)
 * (*) If this key is not present in the tree, this record doesn't
 * reflect the IN state of the tree and this log entry is not applicable.
 * </pre>
 * @param locationholds state about the search in the tree. Passed in from the
 * recovery manager to reduce objection creation overhead.
 * @param lnFromLog -
 * the new node to put in the tree.
 * @param mainKeyis the key that navigates us through the main tree
 * @param dupTreeKeyis the key that navigates us through the duplicate tree
 * @param logLsnis the LSN from the just-read log entry
 * @param abortLsngives us the location of the original version of the node
 * @param infois a recovery stats object.
 */
  public static void undo(  Level traceLevel,  DatabaseImpl db,  TreeLocation location,  LN lnFromLog,  byte[] mainKey,  byte[] dupKey,  long logLsn,  long abortLsn,  boolean abortKnownDeleted,  RecoveryInfo info,  boolean splitsAllowed) throws DatabaseException {
    boolean found=false;
    boolean replaced=false;
    boolean success=false;
    hook584(traceLevel,db,location,lnFromLog,mainKey,dupKey,logLsn,abortLsn,abortKnownDeleted,info,splitsAllowed,found,replaced,success);
  }
  /** 
 * Inserts a LN into the tree for recovery redo processing. In this case, we
 * know we don't have to lock when checking child LNs for deleted status
 * (there can be no other thread running on this tree) and we don't have to
 * log the new entry. (it's in the log already)
 * @param db
 * @param locationthis embodies the parent bin, the index, the key that
 * represents this entry in the bin.
 * @param logLsnLSN of this current ln
 * @param keyto use when creating a new ChildReference object.
 * @return true if LN was inserted, false if it was a duplicate duplicate or
 * if an attempt was made to insert a duplicate when allowDuplicates
 * was false.
 */
  private static boolean insertRecovery(  DatabaseImpl db,  TreeLocation location,  long logLsn) throws DatabaseException {
    ChildReference newLNRef=new ChildReference(null,location.lnKey,logLsn);
    BIN parentBIN=location.bin;
    int entryIndex=parentBIN.insertEntry1(newLNRef);
    if ((entryIndex & IN.INSERT_SUCCESS) == 0) {
      entryIndex&=~IN.EXACT_MATCH;
      boolean canOverwrite=false;
      if (parentBIN.isEntryKnownDeleted(entryIndex)) {
        canOverwrite=true;
      }
 else {
        LN currentLN=(LN)parentBIN.fetchTarget(entryIndex);
        if (currentLN == null || currentLN.isDeleted()) {
          canOverwrite=true;
        }
        parentBIN.updateEntry(entryIndex,null);
      }
      if (canOverwrite) {
        parentBIN.updateEntry(entryIndex,null,logLsn,location.lnKey);
        parentBIN.clearKnownDeleted(entryIndex);
        location.index=entryIndex;
        return true;
      }
 else {
        return false;
      }
    }
    location.index=entryIndex & ~IN.INSERT_SUCCESS;
    return true;
  }
  /** 
 * Update file utilization info during redo.
 */
  private void redoUtilizationInfo(  long logLsn,  long treeLsn,  long abortLsn,  boolean abortKnownDeleted,  LN ln,  TxnNodeId txnNodeId,  Set countedAbortLsnNodes){
    UtilizationTracker tracker=env.getUtilizationTracker();
    if (ln.isDeleted()) {
      Long logFileNum=new Long(DbLsn.getFileNumber(logLsn));
      long fileSummaryLsn=DbLsn.longToLsn((Long)fileSummaryLsns.get(logFileNum));
      int cmpFsLsnToLogLsn=(fileSummaryLsn != DbLsn.NULL_LSN) ? DbLsn.compareTo(fileSummaryLsn,logLsn) : -1;
      if (cmpFsLsnToLogLsn < 0) {
        tracker.countObsoleteNode(logLsn,null);
      }
    }
    if (treeLsn != DbLsn.NULL_LSN) {
      int cmpLogLsnToTreeLsn=DbLsn.compareTo(logLsn,treeLsn);
      if (cmpLogLsnToTreeLsn != 0) {
        long newLsn=(cmpLogLsnToTreeLsn < 0) ? treeLsn : logLsn;
        long oldLsn=(cmpLogLsnToTreeLsn > 0) ? treeLsn : logLsn;
        Long oldLsnFile=new Long(DbLsn.getFileNumber(oldLsn));
        long oldFsLsn=DbLsn.longToLsn((Long)fileSummaryLsns.get(oldLsnFile));
        int cmpOldFsLsnToNewLsn=(oldFsLsn != DbLsn.NULL_LSN) ? DbLsn.compareTo(oldFsLsn,newLsn) : -1;
        if (cmpOldFsLsnToNewLsn < 0) {
          tracker.countObsoleteNode(oldLsn,null);
        }
      }
      if (cmpLogLsnToTreeLsn <= 0 && abortLsn != DbLsn.NULL_LSN && !abortKnownDeleted && !countedAbortLsnNodes.contains(txnNodeId)) {
        Long abortFileNum=new Long(DbLsn.getFileNumber(abortLsn));
        long abortFsLsn=DbLsn.longToLsn((Long)fileSummaryLsns.get(abortFileNum));
        int cmpAbortFsLsnToLogLsn=(abortFsLsn != DbLsn.NULL_LSN) ? DbLsn.compareTo(abortFsLsn,logLsn) : -1;
        if (cmpAbortFsLsnToLogLsn < 0) {
          tracker.countObsoleteNodeInexact(abortLsn,null);
          countedAbortLsnNodes.add(txnNodeId);
        }
      }
    }
  }
  /** 
 * Update file utilization info during recovery undo (not abort undo).
 */
  private void undoUtilizationInfo(  LN ln,  long logLsn,  long abortLsn,  boolean abortKnownDeleted,  TxnNodeId txnNodeId,  Map countedFileSummaries,  Set countedAbortLsnNodes){
    UtilizationTracker tracker=env.getUtilizationTracker();
    Long logFileNum=new Long(DbLsn.getFileNumber(logLsn));
    long fileSummaryLsn=DbLsn.longToLsn((Long)fileSummaryLsns.get(logFileNum));
    int cmpFsLsnToLogLsn=(fileSummaryLsn != DbLsn.NULL_LSN) ? DbLsn.compareTo(fileSummaryLsn,logLsn) : -1;
    if (cmpFsLsnToLogLsn < 0) {
      tracker.countObsoleteNode(logLsn,null);
    }
    if (cmpFsLsnToLogLsn > 0) {
      Long countedFile=(Long)countedFileSummaries.get(txnNodeId);
      if (countedFile == null || countedFile.longValue() > logFileNum.longValue()) {
        if (!ln.isDeleted()) {
          tracker.countObsoleteNode(logLsn,null);
        }
        countedFileSummaries.put(txnNodeId,logFileNum);
      }
    }
  }
  /** 
 * Concoct a header for the recovery pass trace info.
 */
  private String passStartHeader(  int passNum){
    return "Recovery Pass " + passNum + " start: ";
  }
  /** 
 * Concoct a header for the recovery pass trace info.
 */
  private String passEndHeader(  int passNum,  long start,  long end){
    return "Recovery Pass " + passNum + " end ("+ (end - start)+ "): ";
  }
  /** 
 * Send trace messages to the java.util.logger. Don't rely on the logger
 * alone to conditionalize whether we send this message, we don't even want
 * to construct the message if the level is not enabled. This is used to
 * construct verbose trace messages for individual log entry processing.
 */
  private static void trace(  Level level,  DatabaseImpl database,  String debugType,  boolean success,  Node node,  long logLsn,  IN parent,  boolean found,  boolean replaced,  boolean inserted,  long replacedLsn,  long abortLsn,  int index){
    new RecoveryManager_trace(level,database,debugType,success,node,logLsn,parent,found,replaced,inserted,replacedLsn,abortLsn,index).execute();
  }
  private void traceAndThrowException(  long badLsn,  String method,  Exception origException) throws DatabaseException {
    String badLsnString=DbLsn.getNoFormatString(badLsn);
    this.hook577(method,origException,badLsnString);
    throw new DatabaseException("last LSN=" + badLsnString,origException);
  }
@MethodObject static class RecoveryManager_trace {
    RecoveryManager_trace(    Level level,    DatabaseImpl database,    String debugType,    boolean success,    Node node,    long logLsn,    IN parent,    boolean found,    boolean replaced,    boolean inserted,    long replacedLsn,    long abortLsn,    int index){
      this.level=level;
      this.database=database;
      this.debugType=debugType;
      this.success=success;
      this.node=node;
      this.logLsn=logLsn;
      this.parent=parent;
      this.found=found;
      this.replaced=replaced;
      this.inserted=inserted;
      this.replacedLsn=replacedLsn;
      this.abortLsn=abortLsn;
      this.index=index;
    }
    void execute(){
    }
    protected Level level;
    protected DatabaseImpl database;
    protected String debugType;
    protected boolean success;
    protected Node node;
    protected long logLsn;
    protected IN parent;
    protected boolean found;
    protected boolean replaced;
    protected boolean inserted;
    protected long replacedLsn;
    protected long abortLsn;
    protected int index;
    protected Logger logger;
    protected Level useLevel;
    protected StringBuffer sb;
  }
  protected void hook556() throws DatabaseException, IOException {
  }
  protected void hook557(  DatabaseImpl db) throws DatabaseException {
  }
  protected void hook558() throws DatabaseException, IOException {
  }
  protected void hook559() throws DatabaseException, IOException {
  }
  protected void hook560() throws DatabaseException, IOException {
  }
  protected void hook561(  long start,  long end) throws IOException, DatabaseException {
  }
  protected void hook562(  long start,  long end) throws IOException, DatabaseException {
  }
  protected void hook563() throws IOException, DatabaseException {
  }
  protected void hook564(  long start,  long end) throws IOException, DatabaseException {
  }
  protected void hook565(  long start,  long end) throws IOException, DatabaseException {
  }
  protected void hook566(  long start,  long end) throws IOException, DatabaseException {
  }
  protected void hook567(  long start,  long end) throws IOException, DatabaseException {
  }
  protected void hook568(  long start,  long end) throws IOException, DatabaseException {
  }
  protected void hook569(  long start,  long end) throws IOException, DatabaseException {
  }
  protected void hook570(  long start,  long end) throws IOException, DatabaseException {
  }
  protected void hook571(  long start,  long end) throws IOException, DatabaseException {
  }
  protected void hook572() throws IOException, DatabaseException {
  }
  protected void hook573() throws DatabaseException, IOException {
  }
  protected void hook574(  LNFileReader reader) throws IOException, DatabaseException, Exception {
  }
  protected void hook575(  IOException e) throws DatabaseException {
  }
  protected void hook576(  DatabaseImpl db,  long logLsn,  Exception e,  String trace) throws DatabaseException {
  }
  protected void hook577(  String method,  Exception origException,  String badLsnString) throws DatabaseException {
  }
  protected void hook578(  EnvironmentImpl env) throws DatabaseException {
  }
  protected void hook579(  long nodeId,  boolean containsDuplicates,  long logLsn,  boolean found,  boolean deleted,  SearchResult result) throws DatabaseException {
  }
  protected void hook580(  DatabaseImpl db,  IN inFromLog,  long lsn,  boolean success,  RootUpdater rootUpdater) throws DatabaseException {
  }
  protected void hook581(  DatabaseImpl db,  DIN inFromLog,  long lsn,  boolean found,  boolean inserted,  boolean replaced,  long origLsn,  IN parent,  int index,  boolean success) throws DatabaseException {
  }
  protected void hook582(  DatabaseImpl db,  IN inFromLog,  long logLsn,  boolean inserted,  boolean replaced,  long origLsn,  boolean success,  SearchResult result) throws DatabaseException {
  }
  protected void hook583(  DatabaseImpl db,  TreeLocation location,  LN lnFromLog,  long logLsn,  boolean found,  boolean replaced,  boolean inserted,  boolean success) throws DatabaseException {
  }
  protected static void hook584(  Level traceLevel,  DatabaseImpl db,  TreeLocation location,  LN lnFromLog,  byte[] mainKey,  byte[] dupKey,  long logLsn,  long abortLsn,  boolean abortKnownDeleted,  RecoveryInfo info,  boolean splitsAllowed,  boolean found,  boolean replaced,  boolean success) throws DatabaseException {
    location.reset();
    found=db.getTree().getParentBINForChildLN(location,mainKey,dupKey,lnFromLog,splitsAllowed,true,false,true);
    if (lnFromLog.containsDuplicates()) {
      if (found) {
        DIN duplicateRoot=(DIN)location.bin.fetchTarget(location.index);
        replaced=hook592(location,logLsn,abortLsn,replaced,duplicateRoot);
      }
    }
 else {
      if (found) {
        if (info != null) {
          info.lnFound++;
        }
        boolean updateEntry=DbLsn.compareTo(logLsn,location.childLsn) == 0;
        if (updateEntry) {
          if (abortLsn == DbLsn.NULL_LSN) {
            location.bin.setKnownDeletedLeaveTarget(location.index);
            byte[] deletedKey=location.bin.containsDuplicates() ? dupKey : mainKey;
            hook595(db,location,deletedKey);
          }
 else {
            if (info != null) {
              info.lnReplaced++;
            }
            replaced=true;
            location.bin.updateEntry(location.index,null,abortLsn);
            if (abortKnownDeleted) {
              location.bin.setKnownDeleted(location.index);
            }
 else {
              location.bin.clearKnownDeleted(location.index);
            }
          }
          location.bin.clearPendingDeleted(location.index);
        }
      }
 else {
        if (info != null) {
          info.lnNotFound++;
        }
      }
    }
    success=true;
  }
  protected void hook585(  IN in) throws DatabaseException {
  }
  protected void hook586(  RecoveryInfo info,  LNFileReader reader,  TreeLocation location,  LN ln,  long logLsn,  long abortLsn,  boolean abortKnownDeleted,  DatabaseImpl db) throws IOException, DatabaseException, Exception {
    undo(detailedTraceLevel,db,location,ln,reader.getKey(),reader.getDupTreeKey(),logLsn,abortLsn,abortKnownDeleted,info,true);
  }
  protected void hook587(  IN inFromLog,  long logLsn) throws DatabaseException {
  }
  protected void hook588(  SearchResult result) throws DatabaseException {
  }
  protected void hook589(  IN parent) throws DatabaseException {
  }
  protected void hook590(  SearchResult result) throws DatabaseException {
  }
  protected void hook591(  TreeLocation location) throws DatabaseException {
  }
  protected static boolean hook592(  TreeLocation location,  long logLsn,  long abortLsn,  boolean replaced,  DIN duplicateRoot) throws DatabaseException {
    if (DbLsn.compareTo(logLsn,location.childLsn) == 0) {
      duplicateRoot.updateDupCountLNRefAndNullTarget(abortLsn);
      replaced=true;
    }
    return replaced;
  }
  protected void hook593(  INFileReader reader) throws IOException, DatabaseException {
  }
  protected void hook594(  DatabaseImpl db,  TreeLocation location,  byte[] deletedKey) throws DatabaseException {
  }
  protected static void hook595(  DatabaseImpl db,  TreeLocation location,  byte[] deletedKey) throws DatabaseException {
  }
  protected void hook596() throws IOException, DatabaseException {
  }
  protected void hook597() throws IOException, DatabaseException, Exception {
  }
  protected void hook598() throws IOException, DatabaseException, Exception {
  }
}
