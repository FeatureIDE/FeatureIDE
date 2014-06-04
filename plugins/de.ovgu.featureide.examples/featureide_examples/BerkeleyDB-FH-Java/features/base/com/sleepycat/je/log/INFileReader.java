package com.sleepycat.je.log;
import java.io.IOException;
import java.nio.ByteBuffer;
import java.util.HashMap;
import java.util.Map;
import com.sleepycat.je.DatabaseException;
import com.sleepycat.je.cleaner.TrackedFileSummary;
import com.sleepycat.je.cleaner.UtilizationTracker;
import com.sleepycat.je.dbi.DatabaseId;
import com.sleepycat.je.dbi.DbTree;
import com.sleepycat.je.dbi.EnvironmentImpl;
import com.sleepycat.je.log.entry.INContainingEntry;
import com.sleepycat.je.log.entry.INLogEntry;
import com.sleepycat.je.log.entry.LNLogEntry;
import com.sleepycat.je.log.entry.LogEntry;
import com.sleepycat.je.log.entry.NodeLogEntry;
import com.sleepycat.je.tree.FileSummaryLN;
import com.sleepycat.je.tree.IN;
import com.sleepycat.je.tree.INDeleteInfo;
import com.sleepycat.je.tree.INDupDeleteInfo;
import com.sleepycat.je.tree.MapLN;
import com.sleepycat.je.utilint.DbLsn;
import de.ovgu.cide.jakutil.*;
/** 
 * INFileReader supports recovery by scanning log files during the IN rebuild
 * pass. It looks for internal nodes (all types), segregated by whether they
 * belong to the main tree or the duplicate trees.
 * <p>This file reader can also be run in tracking mode to keep track of the
 * maximum node id, database id and txn id seen so those sequences can be
 * updated properly at recovery.  In this mode it also performs utilization
 * counting.  It is only run once in tracking mode per recovery, in the
 * first phase of recovery.</p>
 */
public class INFileReader extends FileReader {
  private boolean lastEntryWasDelete;
  private boolean lastEntryWasDupDelete;
  private LogEntryType fromLogType;
  private boolean isProvisional;
  private Map targetEntryMap;
  private LogEntry targetLogEntry;
  private Map dbIdTrackingMap;
  private LNLogEntry dbIdTrackingEntry;
  private Map txnIdTrackingMap;
  private LNLogEntry txnIdTrackingEntry;
  private Map otherNodeTrackingMap;
  private NodeLogEntry nodeTrackingEntry;
  private INLogEntry inTrackingEntry;
  private LNLogEntry fsTrackingEntry;
  private boolean trackIds;
  private long maxNodeId;
  private int maxDbId;
  private long maxTxnId;
  private boolean mapDbOnly;
  private long partialCkptStart;
  private UtilizationTracker tracker;
  private Map fileSummaryLsns;
  /** 
 * Create this reader to start at a given LSN.
 */
  public INFileReader(  EnvironmentImpl env,  int readBufferSize,  long startLsn,  long finishLsn,  boolean trackIds,  boolean mapDbOnly,  long partialCkptStart,  Map fileSummaryLsns) throws IOException, DatabaseException {
    super(env,readBufferSize,true,startLsn,null,DbLsn.NULL_LSN,finishLsn);
    this.trackIds=trackIds;
    this.mapDbOnly=mapDbOnly;
    targetEntryMap=new HashMap();
    if (trackIds) {
      maxNodeId=0;
      maxDbId=0;
      tracker=env.getUtilizationTracker();
      this.partialCkptStart=partialCkptStart;
      this.fileSummaryLsns=fileSummaryLsns;
      fsTrackingEntry=(LNLogEntry)LogEntryType.LOG_FILESUMMARYLN.getNewLogEntry();
      dbIdTrackingMap=new HashMap();
      txnIdTrackingMap=new HashMap();
      otherNodeTrackingMap=new HashMap();
      dbIdTrackingMap.put(LogEntryType.LOG_MAPLN_TRANSACTIONAL,LogEntryType.LOG_MAPLN_TRANSACTIONAL.getNewLogEntry());
      dbIdTrackingMap.put(LogEntryType.LOG_MAPLN,LogEntryType.LOG_MAPLN.getNewLogEntry());
      txnIdTrackingMap.put(LogEntryType.LOG_LN_TRANSACTIONAL,LogEntryType.LOG_LN_TRANSACTIONAL.getNewLogEntry());
      txnIdTrackingMap.put(LogEntryType.LOG_MAPLN_TRANSACTIONAL,LogEntryType.LOG_MAPLN_TRANSACTIONAL.getNewLogEntry());
      txnIdTrackingMap.put(LogEntryType.LOG_NAMELN_TRANSACTIONAL,LogEntryType.LOG_NAMELN_TRANSACTIONAL.getNewLogEntry());
      txnIdTrackingMap.put(LogEntryType.LOG_DEL_DUPLN_TRANSACTIONAL,LogEntryType.LOG_DEL_DUPLN_TRANSACTIONAL.getNewLogEntry());
      txnIdTrackingMap.put(LogEntryType.LOG_DUPCOUNTLN_TRANSACTIONAL,LogEntryType.LOG_DUPCOUNTLN_TRANSACTIONAL.getNewLogEntry());
    }
  }
  /** 
 * Configure this reader to target this kind of entry.
 */
  public void addTargetType(  LogEntryType entryType) throws DatabaseException {
    targetEntryMap.put(entryType,entryType.getNewLogEntry());
  }
  /** 
 * If we're tracking node, database and txn ids, we want to see all node
 * log entries. If not, we only want to see IN entries.
 * @return true if this is an IN entry.
 */
  protected boolean isTargetEntry(  byte entryTypeNum,  byte entryTypeVersion) throws DatabaseException {
    lastEntryWasDelete=false;
    lastEntryWasDupDelete=false;
    targetLogEntry=null;
    dbIdTrackingEntry=null;
    txnIdTrackingEntry=null;
    nodeTrackingEntry=null;
    inTrackingEntry=null;
    fsTrackingEntry=null;
    isProvisional=LogEntryType.isProvisional(entryTypeVersion);
    fromLogType=LogEntryType.findType(entryTypeNum,entryTypeVersion);
    LogEntry possibleTarget=(LogEntry)targetEntryMap.get(fromLogType);
    if (!isProvisional) {
      targetLogEntry=possibleTarget;
    }
    if (LogEntryType.LOG_IN_DELETE_INFO.equals(fromLogType)) {
      lastEntryWasDelete=true;
    }
    if (LogEntryType.LOG_IN_DUPDELETE_INFO.equals(fromLogType)) {
      lastEntryWasDupDelete=true;
    }
    if (trackIds) {
      if (!isProvisional) {
        dbIdTrackingEntry=(LNLogEntry)dbIdTrackingMap.get(fromLogType);
        txnIdTrackingEntry=(LNLogEntry)txnIdTrackingMap.get(fromLogType);
      }
      if (fromLogType.isNodeType()) {
        if (possibleTarget != null) {
          nodeTrackingEntry=(NodeLogEntry)possibleTarget;
        }
 else         if (dbIdTrackingEntry != null) {
          nodeTrackingEntry=dbIdTrackingEntry;
        }
 else         if (txnIdTrackingEntry != null) {
          nodeTrackingEntry=txnIdTrackingEntry;
        }
 else {
          nodeTrackingEntry=(NodeLogEntry)otherNodeTrackingMap.get(fromLogType);
          if (nodeTrackingEntry == null) {
            nodeTrackingEntry=(NodeLogEntry)fromLogType.getNewLogEntry();
            otherNodeTrackingMap.put(fromLogType,nodeTrackingEntry);
          }
        }
        if (nodeTrackingEntry instanceof INLogEntry) {
          inTrackingEntry=(INLogEntry)nodeTrackingEntry;
        }
        if (LogEntryType.LOG_FILESUMMARYLN.equals(fromLogType)) {
          fsTrackingEntry=(LNLogEntry)nodeTrackingEntry;
        }
      }
      tracker.countNewLogEntry(getLastLsn(),fromLogType,LogManager.HEADER_BYTES + currentEntrySize);
      return (targetLogEntry != null) || (dbIdTrackingEntry != null) || (txnIdTrackingEntry != null)|| (nodeTrackingEntry != null);
    }
 else {
      return (targetLogEntry != null);
    }
  }
  /** 
 * This reader looks at all nodes for the max node id and database id. It
 * only returns non-provisional INs and IN delete entries.
 */
  protected boolean processEntry(  ByteBuffer entryBuffer) throws DatabaseException {
    boolean useEntry=false;
    boolean entryLoaded=false;
    if (targetLogEntry != null) {
      targetLogEntry.readEntry(entryBuffer,currentEntrySize,currentEntryTypeVersion,true);
      DatabaseId dbId=getDatabaseId();
      boolean isMapDb=dbId.equals(DbTree.ID_DB_ID);
      useEntry=(!mapDbOnly || isMapDb);
      entryLoaded=true;
    }
    if (trackIds) {
      LNLogEntry lnEntry=null;
      if (dbIdTrackingEntry != null) {
        lnEntry=dbIdTrackingEntry;
        lnEntry.readEntry(entryBuffer,currentEntrySize,currentEntryTypeVersion,true);
        entryLoaded=true;
        MapLN mapLN=(MapLN)lnEntry.getMainItem();
        int dbId=mapLN.getDatabase().getId().getId();
        if (dbId > maxDbId) {
          maxDbId=dbId;
        }
      }
      if (txnIdTrackingEntry != null) {
        if (lnEntry == null) {
          lnEntry=txnIdTrackingEntry;
          lnEntry.readEntry(entryBuffer,currentEntrySize,currentEntryTypeVersion,true);
          entryLoaded=true;
        }
        long txnId=lnEntry.getTxnId().longValue();
        if (txnId > maxTxnId) {
          maxTxnId=txnId;
        }
      }
      if (fsTrackingEntry != null) {
        if (!entryLoaded) {
          nodeTrackingEntry.readEntry(entryBuffer,currentEntrySize,currentEntryTypeVersion,true);
          entryLoaded=true;
        }
        byte[] keyBytes=fsTrackingEntry.getKey();
        FileSummaryLN fsln=(FileSummaryLN)fsTrackingEntry.getMainItem();
        long fileNum=fsln.getFileNumber(keyBytes);
        TrackedFileSummary trackedLN=tracker.getTrackedFile(fileNum);
        if (trackedLN != null) {
          trackedLN.reset();
        }
        fileSummaryLsns.put(new Long(fileNum),new Long(getLastLsn()));
      }
      if (nodeTrackingEntry != null) {
        if (!entryLoaded) {
          nodeTrackingEntry.readEntry(entryBuffer,currentEntrySize,currentEntryTypeVersion,false);
          entryLoaded=true;
        }
        long nodeId=nodeTrackingEntry.getNodeId();
        maxNodeId=(nodeId > maxNodeId) ? nodeId : maxNodeId;
      }
      if (inTrackingEntry != null) {
        assert entryLoaded : "All nodes should have been loaded";
        long oldLsn=inTrackingEntry.getObsoleteLsn();
        if (oldLsn != DbLsn.NULL_LSN) {
          long newLsn=getLastLsn();
          if (!isObsoleteLsnAlreadyCounted(oldLsn,newLsn)) {
            tracker.countObsoleteNodeInexact(oldLsn,fromLogType);
          }
        }
        if (isProvisional && partialCkptStart != DbLsn.NULL_LSN) {
          oldLsn=getLastLsn();
          if (DbLsn.compareTo(partialCkptStart,oldLsn) < 0) {
            tracker.countObsoleteNodeInexact(oldLsn,fromLogType);
          }
        }
      }
    }
    return useEntry;
  }
  /** 
 * Returns whether a given obsolete LSN has already been counted in the
 * utilization profile.  If true is returned, it should not be counted
 * again, to prevent double-counting.
 */
  private boolean isObsoleteLsnAlreadyCounted(  long oldLsn,  long newLsn){
    Long fileNum=new Long(DbLsn.getFileNumber(oldLsn));
    long fileSummaryLsn=DbLsn.longToLsn((Long)fileSummaryLsns.get(fileNum));
    int cmpFsLsnToNewLsn=(fileSummaryLsn != DbLsn.NULL_LSN) ? DbLsn.compareTo(fileSummaryLsn,newLsn) : -1;
    return (cmpFsLsnToNewLsn >= 0);
  }
  /** 
 * Get the last IN seen by the reader.
 */
  public IN getIN() throws DatabaseException {
    return ((INContainingEntry)targetLogEntry).getIN(env);
  }
  /** 
 * Get the last databaseId seen by the reader.
 */
  public DatabaseId getDatabaseId(){
    if (lastEntryWasDelete) {
      return ((INDeleteInfo)targetLogEntry.getMainItem()).getDatabaseId();
    }
 else     if (lastEntryWasDupDelete) {
      return ((INDupDeleteInfo)targetLogEntry.getMainItem()).getDatabaseId();
    }
 else {
      return ((INContainingEntry)targetLogEntry).getDbId();
    }
  }
  /** 
 * Get the maximum node id seen by the reader.
 */
  public long getMaxNodeId(){
    return maxNodeId;
  }
  /** 
 * Get the maximum db id seen by the reader.
 */
  public int getMaxDbId(){
    return maxDbId;
  }
  /** 
 * Get the maximum txn id seen by the reader.
 */
  public long getMaxTxnId(){
    return maxTxnId;
  }
  /** 
 * @return true if the last entry was a delete info entry.
 */
  public boolean isDeleteInfo(){
    return lastEntryWasDelete;
  }
  /** 
 * @return true if the last entry was a dup delete info entry.
 */
  public boolean isDupDeleteInfo(){
    return lastEntryWasDupDelete;
  }
  /** 
 * Get the deleted node id stored in the last delete info log entry.
 */
  public long getDeletedNodeId(){
    return ((INDeleteInfo)targetLogEntry.getMainItem()).getDeletedNodeId();
  }
  /** 
 * Get the deleted id key stored in the last delete info log entry.
 */
  public byte[] getDeletedIdKey(){
    return ((INDeleteInfo)targetLogEntry.getMainItem()).getDeletedIdKey();
  }
  /** 
 * Get the deleted node id stored in the last delete info log entry.
 */
  public long getDupDeletedNodeId(){
    return ((INDupDeleteInfo)targetLogEntry.getMainItem()).getDeletedNodeId();
  }
  /** 
 * Get the deleted main key stored in the last delete info log entry.
 */
  public byte[] getDupDeletedMainKey(){
    return ((INDupDeleteInfo)targetLogEntry.getMainItem()).getDeletedMainKey();
  }
  /** 
 * Get the deleted main key stored in the last delete info log entry.
 */
  public byte[] getDupDeletedDupKey(){
    return ((INDupDeleteInfo)targetLogEntry.getMainItem()).getDeletedDupKey();
  }
  /** 
 * Get the LSN that should represent this IN. For most INs, it's the LSN
 * that was just read. For BINDelta entries, it's the LSN of the last
 * full version.
 */
  public long getLsnOfIN(){
    return ((INContainingEntry)targetLogEntry).getLsnOfIN(getLastLsn());
  }
  /** 
 * Get the current log entry type.
 */
  public LogEntryType getLogEntryType(){
    return LogEntryType.findType(currentEntryTypeNum,currentEntryTypeVersion);
  }
}
