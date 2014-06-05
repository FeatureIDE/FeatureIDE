package com.sleepycat.je.dbi;
import java.io.PrintStream;
import java.nio.ByteBuffer;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;
import com.sleepycat.je.Cursor;
import com.sleepycat.je.Database;
import com.sleepycat.je.DatabaseConfig;
import com.sleepycat.je.DatabaseEntry;
import com.sleepycat.je.DatabaseException;
import com.sleepycat.je.DbInternal;
import com.sleepycat.je.LockMode;
import com.sleepycat.je.OperationStatus;
import com.sleepycat.je.PreloadConfig;
import com.sleepycat.je.PreloadStats;
import com.sleepycat.je.PreloadStatus;
import com.sleepycat.je.SecondaryDatabase;
import com.sleepycat.je.cleaner.UtilizationTracker;
import com.sleepycat.je.config.EnvironmentParams;
import com.sleepycat.je.dbi.SortedLSNTreeWalker.TreeNodeProcessor;
import com.sleepycat.je.log.LogEntryType;
import com.sleepycat.je.log.LogException;
import com.sleepycat.je.log.LogReadable;
import com.sleepycat.je.log.LogUtils;
import com.sleepycat.je.log.LogWritable;
import com.sleepycat.je.tree.ChildReference;
import com.sleepycat.je.tree.Node;
import com.sleepycat.je.tree.Tree;
import com.sleepycat.je.tree.TreeUtils;
import com.sleepycat.je.tree.TreeWalkerStatsAccumulator;
import com.sleepycat.je.tree.WithRootLatched;
import com.sleepycat.je.txn.Locker;
import com.sleepycat.je.txn.ThreadLocker;
import com.sleepycat.je.utilint.CmdUtil;
import com.sleepycat.je.utilint.DbLsn;
import com.sleepycat.je.utilint.TestHook;
import de.ovgu.cide.jakutil.*;
/** 
 * The underlying object for a given database.
 */
public class DatabaseImpl implements LogWritable, LogReadable, Cloneable {
  private DatabaseId id;
  Tree tree;
  private EnvironmentImpl envImpl;
  private boolean duplicatesAllowed;
  private boolean transactional;
  private Set referringHandles;
  private long eofNodeId;
  private Comparator btreeComparator=null;
  private Comparator duplicateComparator=null;
  private String btreeComparatorName="";
  private String duplicateComparatorName="";
  private int binDeltaPercent;
  private int binMaxDeltas;
  private int maxMainTreeEntriesPerNode;
  private int maxDupTreeEntriesPerNode;
  private String debugDatabaseName;
  private TestHook pendingDeletedHook;
  /** 
 * Create a database object for a new database.
 */
  public DatabaseImpl(  String dbName,  DatabaseId id,  EnvironmentImpl envImpl,  DatabaseConfig dbConfig) throws DatabaseException {
    this.id=id;
    this.envImpl=envImpl;
    this.btreeComparator=dbConfig.getBtreeComparator();
    this.duplicateComparator=dbConfig.getDuplicateComparator();
    duplicatesAllowed=dbConfig.getSortedDuplicates();
    transactional=dbConfig.getTransactional();
    maxMainTreeEntriesPerNode=dbConfig.getNodeMaxEntries();
    maxDupTreeEntriesPerNode=dbConfig.getNodeMaxDupTreeEntries();
    initDefaultSettings();
    this.hook288();
    tree=new Tree(this);
    referringHandles=Collections.synchronizedSet(new HashSet());
    eofNodeId=Node.getNextNodeId();
    debugDatabaseName=dbName;
  }
  /** 
 * Create an empty database object for initialization from the log. Note
 * that the rest of the initialization comes from readFromLog(), except for
 * the debugDatabaseName, which is set by the caller.
 */
  public DatabaseImpl() throws DatabaseException {
    id=new DatabaseId();
    envImpl=null;
    this.hook289();
    tree=new Tree();
    referringHandles=Collections.synchronizedSet(new HashSet());
    eofNodeId=Node.getNextNodeId();
  }
  public void setDebugDatabaseName(  String debugName){
    debugDatabaseName=debugName;
  }
  public String getDebugName(){
    return debugDatabaseName;
  }
  public void setPendingDeletedHook(  TestHook hook){
    pendingDeletedHook=hook;
  }
  /** 
 * Initialize configuration settings when creating a new instance or after
 * reading an instance from the log. The envImpl field must be set before
 * calling this method.
 */
  private void initDefaultSettings() throws DatabaseException {
    DbConfigManager configMgr=envImpl.getConfigManager();
    binDeltaPercent=configMgr.getInt(EnvironmentParams.BIN_DELTA_PERCENT);
    binMaxDeltas=configMgr.getInt(EnvironmentParams.BIN_MAX_DELTAS);
    if (maxMainTreeEntriesPerNode == 0) {
      maxMainTreeEntriesPerNode=configMgr.getInt(EnvironmentParams.NODE_MAX);
    }
    if (maxDupTreeEntriesPerNode == 0) {
      maxDupTreeEntriesPerNode=configMgr.getInt(EnvironmentParams.NODE_MAX_DUPTREE);
    }
  }
  /** 
 * Clone. For now just pass off to the super class for a field-by-field
 * copy.
 */
  public Object clone() throws CloneNotSupportedException {
    return super.clone();
  }
  /** 
 * @return the database tree.
 */
  public Tree getTree(){
    return tree;
  }
  void setTree(  Tree tree){
    this.tree=tree;
  }
  /** 
 * @return the database id.
 */
  public DatabaseId getId(){
    return id;
  }
  void setId(  DatabaseId id){
    this.id=id;
  }
  public long getEofNodeId(){
    return eofNodeId;
  }
  /** 
 * @return true if this database is transactional.
 */
  public boolean isTransactional(){
    return transactional;
  }
  /** 
 * Sets the transactional property for the first opened handle.
 */
  public void setTransactional(  boolean transactional){
    this.transactional=transactional;
  }
  /** 
 * @return true if duplicates are allowed in this database.
 */
  public boolean getSortedDuplicates(){
    return duplicatesAllowed;
  }
  public int getNodeMaxEntries(){
    return maxMainTreeEntriesPerNode;
  }
  public int getNodeMaxDupTreeEntries(){
    return maxDupTreeEntriesPerNode;
  }
  /** 
 * Set the duplicate comparison function for this database.
 * @param duplicateComparator -
 * The Duplicate Comparison function.
 */
  public void setDuplicateComparator(  Comparator duplicateComparator){
    this.duplicateComparator=duplicateComparator;
  }
  /** 
 * Set the btree comparison function for this database.
 * @param btreeComparator -
 * The btree Comparison function.
 */
  public void setBtreeComparator(  Comparator btreeComparator){
    this.btreeComparator=btreeComparator;
  }
  /** 
 * @return the btree Comparator object.
 */
  public Comparator getBtreeComparator(){
    return btreeComparator;
  }
  /** 
 * @return the duplicate Comparator object.
 */
  public Comparator getDuplicateComparator(){
    return duplicateComparator;
  }
  /** 
 * Set the db environment during recovery, after instantiating the database
 * from the log
 */
  public void setEnvironmentImpl(  EnvironmentImpl envImpl) throws DatabaseException {
    this.envImpl=envImpl;
    initDefaultSettings();
    tree.setDatabase(this);
  }
  /** 
 * @return the database environment.
 */
  public EnvironmentImpl getDbEnvironment(){
    return envImpl;
  }
  /** 
 * Returns whether one or more handles are open.
 */
  public boolean hasOpenHandles(){
    return referringHandles.size() > 0;
  }
  /** 
 * Add a referring handle
 */
  public void addReferringHandle(  Database db){
    referringHandles.add(db);
  }
  /** 
 * Decrement the reference count.
 */
  public void removeReferringHandle(  Database db){
    referringHandles.remove(db);
  }
  /** 
 * @return the referring handle count.
 */
  synchronized int getReferringHandleCount(){
    return referringHandles.size();
  }
  /** 
 * For this secondary database return the primary that it is associated
 * with, or null if not associated with any primary. Note that not all
 * handles need be associated with a primary.
 */
  public Database findPrimaryDatabase() throws DatabaseException {
    for (Iterator i=referringHandles.iterator(); i.hasNext(); ) {
      Object obj=i.next();
      if (obj instanceof SecondaryDatabase) {
        return ((SecondaryDatabase)obj).getPrimaryDatabase();
      }
    }
    return null;
  }
  public String getName() throws DatabaseException {
    return envImpl.getDbMapTree().getDbName(id);
  }
private static class ObsoleteProcessor implements TreeNodeProcessor {
    private UtilizationTracker tracker;
    ObsoleteProcessor(    UtilizationTracker tracker){
      this.tracker=tracker;
    }
    public void processLSN(    long childLsn,    LogEntryType childType){
      assert childLsn != DbLsn.NULL_LSN;
      tracker.countObsoleteNodeInexact(childLsn,childType);
    }
  }
  /** 
 * Return the count of nodes in the database. Used for truncate, perhaps
 * should be made available through other means? Database should be
 * quiescent.
 */
  long countRecords() throws DatabaseException {
    LNCounter lnCounter=new LNCounter();
    SortedLSNTreeWalker walker=new SortedLSNTreeWalker(this,false,false,tree.getRootLsn(),lnCounter);
    walker.walk();
    return lnCounter.getCount();
  }
private static class LNCounter implements TreeNodeProcessor {
    private long counter;
    public void processLSN(    long childLsn,    LogEntryType childType){
      assert childLsn != DbLsn.NULL_LSN;
      if (childType.equals(LogEntryType.LOG_LN_TRANSACTIONAL) || childType.equals(LogEntryType.LOG_LN)) {
        counter++;
      }
    }
    long getCount(){
      return counter;
    }
  }
  private boolean walkDatabaseTree(  TreeWalkerStatsAccumulator statsAcc,  PrintStream out,  boolean verbose) throws DatabaseException {
    boolean ok=true;
    Locker locker=new ThreadLocker(envImpl);
    Cursor cursor=null;
    CursorImpl impl=null;
    try {
      EnvironmentImpl.incThreadLocalReferenceCount();
      cursor=DbInternal.newCursor(this,locker,null);
      impl=DbInternal.getCursorImpl(cursor);
      tree.setTreeStatsAccumulator(statsAcc);
      impl.setTreeStatsAccumulator(statsAcc);
      DatabaseEntry foundData=new DatabaseEntry();
      DatabaseEntry key=new DatabaseEntry();
      OperationStatus status=DbInternal.position(cursor,key,foundData,LockMode.READ_UNCOMMITTED,true);
      while (status == OperationStatus.SUCCESS) {
        try {
          status=DbInternal.retrieveNext(cursor,key,foundData,LockMode.READ_UNCOMMITTED,GetMode.NEXT);
        }
 catch (        DatabaseException DBE) {
          ok=false;
          if (DbInternal.advanceCursor(cursor,key,foundData)) {
            if (verbose) {
              out.println("Error encountered (continuing):");
              out.println(DBE);
              printErrorRecord(out,key,foundData);
            }
          }
 else {
            throw DBE;
          }
        }
      }
    }
  finally {
      if (impl != null) {
        impl.setTreeStatsAccumulator(null);
      }
      tree.setTreeStatsAccumulator(null);
      EnvironmentImpl.decThreadLocalReferenceCount();
      if (cursor != null) {
        cursor.close();
      }
    }
    return ok;
  }
  /** 
 * Prints the key and data, if available, for a BIN entry that could not be
 * read/verified. Uses the same format as DbDump and prints both the hex and
 * printable versions of the entries.
 */
  private void printErrorRecord(  PrintStream out,  DatabaseEntry key,  DatabaseEntry data){
    byte[] bytes=key.getData();
    StringBuffer sb=new StringBuffer("Error Key ");
    if (bytes == null) {
      sb.append("UNKNOWN");
    }
 else {
      CmdUtil.formatEntry(sb,bytes,false);
      sb.append(' ');
      CmdUtil.formatEntry(sb,bytes,true);
    }
    out.println(sb);
    bytes=data.getData();
    sb=new StringBuffer("Error Data ");
    if (bytes == null) {
      sb.append("UNKNOWN");
    }
 else {
      CmdUtil.formatEntry(sb,bytes,false);
      sb.append(' ');
      CmdUtil.formatEntry(sb,bytes,true);
    }
    out.println(sb);
  }
  /** 
 * Undeclared exception used to throw through SortedLSNTreeWalker code when
 * preload has either filled the user's max byte or time request.
 */
private static class HaltPreloadException extends RuntimeException {
    private PreloadStatus status;
    HaltPreloadException(    PreloadStatus status){
      super(status.toString());
      this.status=status;
    }
    PreloadStatus getStatus(){
      return status;
    }
  }
  static final HaltPreloadException timeExceededPreloadException=new HaltPreloadException(PreloadStatus.EXCEEDED_TIME);
  static final HaltPreloadException memoryExceededPreloadException=new HaltPreloadException(PreloadStatus.FILLED_CACHE);
  /** 
 * Preload the cache, using up to maxBytes bytes or maxMillsecs msec.
 */
  public PreloadStats preload(  PreloadConfig config) throws DatabaseException {
    return new DatabaseImpl_preload(this,config).execute();
  }
  public String dumpString(  int nSpaces){
    StringBuffer sb=new StringBuffer();
    sb.append(TreeUtils.indent(nSpaces));
    sb.append("<database id=\"");
    sb.append(id.toString());
    sb.append("\"");
    if (btreeComparator != null) {
      sb.append(" btc=\"");
      sb.append(serializeComparator(btreeComparator));
      sb.append("\"");
    }
    if (duplicateComparator != null) {
      sb.append(" dupc=\"");
      sb.append(serializeComparator(duplicateComparator));
      sb.append("\"");
    }
    sb.append("/>");
    return sb.toString();
  }
  /** 
 * @see LogWritable#getLogSize
 */
  public int getLogSize(){
    return id.getLogSize() + tree.getLogSize() + LogUtils.getBooleanLogSize()+ LogUtils.getStringLogSize(serializeComparator(btreeComparator))+ LogUtils.getStringLogSize(serializeComparator(duplicateComparator))+ (LogUtils.getIntLogSize() * 2);
  }
  /** 
 * @see LogWritable#writeToLog
 */
  public void writeToLog(  ByteBuffer logBuffer){
    id.writeToLog(logBuffer);
    tree.writeToLog(logBuffer);
    LogUtils.writeBoolean(logBuffer,duplicatesAllowed);
    LogUtils.writeString(logBuffer,serializeComparator(btreeComparator));
    LogUtils.writeString(logBuffer,serializeComparator(duplicateComparator));
    LogUtils.writeInt(logBuffer,maxMainTreeEntriesPerNode);
    LogUtils.writeInt(logBuffer,maxDupTreeEntriesPerNode);
  }
  /** 
 * @see LogReadable#readFromLog
 */
  public void readFromLog(  ByteBuffer itemBuffer,  byte entryTypeVersion) throws LogException {
    id.readFromLog(itemBuffer,entryTypeVersion);
    tree.readFromLog(itemBuffer,entryTypeVersion);
    duplicatesAllowed=LogUtils.readBoolean(itemBuffer);
    btreeComparatorName=LogUtils.readString(itemBuffer);
    duplicateComparatorName=LogUtils.readString(itemBuffer);
    try {
      if (!EnvironmentImpl.getNoComparators()) {
        if (btreeComparatorName.length() != 0) {
          Class btreeComparatorClass=Class.forName(btreeComparatorName);
          btreeComparator=instantiateComparator(btreeComparatorClass,"Btree");
        }
        if (duplicateComparatorName.length() != 0) {
          Class duplicateComparatorClass=Class.forName(duplicateComparatorName);
          duplicateComparator=instantiateComparator(duplicateComparatorClass,"Duplicate");
        }
      }
    }
 catch (    ClassNotFoundException CNFE) {
      throw new LogException("couldn't instantiate class comparator",CNFE);
    }
    if (entryTypeVersion >= 1) {
      maxMainTreeEntriesPerNode=LogUtils.readInt(itemBuffer);
      maxDupTreeEntriesPerNode=LogUtils.readInt(itemBuffer);
    }
  }
  /** 
 * @see LogReadable#dumpLog
 */
  public void dumpLog(  StringBuffer sb,  boolean verbose){
    sb.append("<database>");
    id.dumpLog(sb,verbose);
    tree.dumpLog(sb,verbose);
    sb.append("<dupsort v=\"").append(duplicatesAllowed);
    sb.append("\"/>");
    sb.append("<btcf name=\"");
    sb.append(btreeComparatorName);
    sb.append("\"/>");
    sb.append("<dupcf name=\"");
    sb.append(duplicateComparatorName);
    sb.append("\"/>");
    sb.append("</database>");
  }
  /** 
 * @see LogReadable#logEntryIsTransactional
 */
  public boolean logEntryIsTransactional(){
    return false;
  }
  /** 
 * @see LogReadable#getTransactionId
 */
  public long getTransactionId(){
    return 0;
  }
  /** 
 * Used both to write to the log and to validate a comparator when set in
 * DatabaseConfig.
 */
  public static String serializeComparator(  Comparator comparator){
    if (comparator != null) {
      return comparator.getClass().getName();
    }
 else {
      return "";
    }
  }
  /** 
 * Used both to read from the log and to validate a comparator when set in
 * DatabaseConfig.
 */
  public static Comparator instantiateComparator(  Class comparator,  String comparatorType) throws LogException {
    if (comparator == null) {
      return null;
    }
    try {
      return (Comparator)comparator.newInstance();
    }
 catch (    InstantiationException IE) {
      throw new LogException("Exception while trying to load " + comparatorType + " Comparator class: "+ IE);
    }
catch (    IllegalAccessException IAE) {
      throw new LogException("Exception while trying to load " + comparatorType + " Comparator class: "+ IAE);
    }
  }
  public int getBinDeltaPercent(){
    return binDeltaPercent;
  }
  public int getBinMaxDeltas(){
    return binMaxDeltas;
  }
@MethodObject static class DatabaseImpl_preload {
    DatabaseImpl_preload(    DatabaseImpl _this,    PreloadConfig config){
      this._this=_this;
      this.config=config;
    }
    PreloadStats execute() throws DatabaseException {
      maxBytes=config.getMaxBytes();
      maxMillisecs=config.getMaxMillisecs();
      targetTime=Long.MAX_VALUE;
      if (maxMillisecs > 0) {
        targetTime=System.currentTimeMillis() + maxMillisecs;
      }
      this.hook290();
      ret=new PreloadStats();
      callback=new PreloadProcessor(_this.envImpl,maxBytes,targetTime,ret);
      walker=new PreloadLSNTreeWalker(_this,callback,config);
      this.hook287();
      return ret;
    }
    protected DatabaseImpl _this;
    protected PreloadConfig config;
    protected long maxBytes;
    protected long maxMillisecs;
    protected long targetTime;
    protected long cacheBudget;
    protected PreloadStats ret;
    protected PreloadProcessor callback;
    protected SortedLSNTreeWalker walker;
    protected void hook287() throws DatabaseException {
      walker.walk();
    }
    protected void hook290() throws DatabaseException {
    }
  }
  protected void hook288() throws DatabaseException {
  }
  protected void hook289() throws DatabaseException {
  }
}
