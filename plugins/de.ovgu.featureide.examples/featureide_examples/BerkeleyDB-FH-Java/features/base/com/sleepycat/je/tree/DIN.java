package com.sleepycat.je.tree;
import java.nio.ByteBuffer;
import java.util.Comparator;
import com.sleepycat.je.DatabaseException;
import com.sleepycat.je.cleaner.Cleaner;
import com.sleepycat.je.dbi.DatabaseId;
import com.sleepycat.je.dbi.DatabaseImpl;
import com.sleepycat.je.dbi.DbConfigManager;
import com.sleepycat.je.dbi.MemoryBudget;
import com.sleepycat.je.log.LogEntryType;
import com.sleepycat.je.log.LogException;
import com.sleepycat.je.log.LogManager;
import com.sleepycat.je.log.LogUtils;
import com.sleepycat.je.txn.LockResult;
import com.sleepycat.je.txn.Locker;
import de.ovgu.cide.jakutil.*;
/** 
 * An DIN represents an Duplicate Internal Node in the JE tree.
 */
public final class DIN extends IN {
  private static final String BEGIN_TAG="<din>";
  private static final String END_TAG="</din>";
  /** 
 * Full key for this set of duplicates.
 */
  private byte[] dupKey;
  /** 
 * Reference to DupCountLN which stores the count.
 */
  private ChildReference dupCountLNRef;
  /** 
 * Create an empty DIN, with no node id, to be filled in from the log.
 */
  public DIN(){
    super();
    dupCountLNRef=new ChildReference();
    init(null,Key.EMPTY_KEY,0,0);
  }
  /** 
 * Create a new DIN.
 */
  public DIN(  DatabaseImpl db,  byte[] identifierKey,  int capacity,  byte[] dupKey,  ChildReference dupCountLNRef,  int level){
    super(db,identifierKey,capacity,level);
    this.dupKey=dupKey;
    this.dupCountLNRef=dupCountLNRef;
  }
  protected int generateLevel(  DatabaseId dbId,  int newLevel){
    return newLevel;
  }
  /** 
 * Create a new DIN.  Need this because we can't call newInstance()
 * without getting a 0 node.
 */
  protected IN createNewInstance(  byte[] identifierKey,  int maxEntries,  int level){
    return new DIN(getDatabase(),identifierKey,maxEntries,dupKey,dupCountLNRef,level);
  }
  /** 
 * Return the key for this duplicate set.
 */
  public byte[] getDupKey(){
    return dupKey;
  }
  /** 
 * Get the key (dupe or identifier) in child that is used to locate
 * it in 'this' node.
 */
  public byte[] getChildKey(  IN child) throws DatabaseException {
    return child.getIdentifierKey();
  }
  public byte[] selectKey(  byte[] mainTreeKey,  byte[] dupTreeKey){
    return dupTreeKey;
  }
  /** 
 * Return the key for navigating through the duplicate tree.
 */
  public byte[] getDupTreeKey(){
    return getIdentifierKey();
  }
  /** 
 * Return the key for navigating through the main tree.
 */
  public byte[] getMainTreeKey(){
    return dupKey;
  }
  public ChildReference getDupCountLNRef(){
    return dupCountLNRef;
  }
  public DupCountLN getDupCountLN() throws DatabaseException {
    return (DupCountLN)dupCountLNRef.fetchTarget(getDatabase(),this);
  }
  /** 
 * Assign the Dup Count LN.
 */
  void setDupCountLN(  ChildReference dupCountLNRef){
    this.dupCountLNRef=dupCountLNRef;
  }
  /** 
 * Assign the Dup Count LN node.  Does not dirty the DIN.
 */
  public void updateDupCountLN(  Node target){
    new DIN_updateDupCountLN(this,target).execute();
  }
  /** 
 * Update Dup Count LN.
 */
  public void updateDupCountLNRefAndNullTarget(  long newLsn){
    new DIN_updateDupCountLNRefAndNullTarget(this,newLsn).execute();
  }
  /** 
 * Update dup count LSN.
 */
  public void updateDupCountLNRef(  long newLsn){
    setDirty(true);
    dupCountLNRef.setLsn(newLsn);
  }
  /** 
 * @return true if this node is a duplicate-bearing node type, false
 * if otherwise.
 */
  public boolean containsDuplicates(){
    return true;
  }
  public boolean isDbRoot(){
    return false;
  }
  /** 
 * Return the comparator function to be used for DINs.  This is
 * the user defined duplicate comparison function, if defined.
 */
  public final Comparator getKeyComparator(){
    return getDatabase().getDuplicateComparator();
  }
  /** 
 * Increment or decrement the DupCountLN, log the updated LN, and update
 * the lock result.
 * Preconditions: This DIN is latched and the DupCountLN is write locked.
 * Postconditions: Same as preconditions.
 */
  public void incrementDuplicateCount(  LockResult lockResult,  byte[] key,  Locker locker,  boolean increment) throws DatabaseException {
    long oldLsn=dupCountLNRef.getLsn();
    lockResult.setAbortLsn(oldLsn,dupCountLNRef.isKnownDeleted());
    DupCountLN dupCountLN=getDupCountLN();
    if (increment) {
      dupCountLN.incDupCount();
    }
 else {
      dupCountLN.decDupCount();
      assert dupCountLN.getDupCount() >= 0;
    }
    DatabaseImpl db=getDatabase();
    long newCountLSN=dupCountLN.log(db.getDbEnvironment(),db.getId(),key,oldLsn,locker);
    updateDupCountLNRef(newCountLSN);
  }
  boolean matchLNByNodeId(  TreeLocation location,  long nodeId) throws DatabaseException {
    for (int i=0; i < getNEntries(); i++) {
      Node n=fetchTarget(i);
      if (n != null) {
        boolean ret=n.matchLNByNodeId(location,nodeId);
        if (ret) {
          return true;
        }
      }
    }
    return false;
  }
  void accumulateStats(  TreeWalkerStatsAccumulator acc){
    acc.processDIN(this,new Long(getNodeId()),getLevel());
  }
  /** 
 * @see IN#getLogType
 */
  public LogEntryType getLogType(){
    return LogEntryType.LOG_DIN;
  }
  /** 
 * Handles lazy migration of DupCountLNs prior to logging a DIN.  See
 * BIN.logInternal for more information.
 */
  protected long logInternal(  LogManager logManager,  boolean allowDeltas,  boolean isProvisional,  boolean proactiveMigration,  IN parent) throws DatabaseException {
    if (dupCountLNRef != null) {
      Cleaner cleaner=getDatabase().getDbEnvironment().getCleaner();
      cleaner.lazyMigrateDupCountLN(this,dupCountLNRef,proactiveMigration);
    }
    return super.logInternal(logManager,allowDeltas,isProvisional,proactiveMigration,parent);
  }
  /** 
 * @see IN#getLogSize
 */
  public int getLogSize(){
    int size=super.getLogSize();
    size+=LogUtils.getByteArrayLogSize(dupKey);
    size+=LogUtils.getBooleanLogSize();
    if (dupCountLNRef != null) {
      size+=dupCountLNRef.getLogSize();
    }
    return size;
  }
  /** 
 * @see IN#writeToLog
 */
  public void writeToLog(  ByteBuffer logBuffer){
    super.writeToLog(logBuffer);
    LogUtils.writeByteArray(logBuffer,dupKey);
    boolean dupCountLNRefExists=(dupCountLNRef != null);
    LogUtils.writeBoolean(logBuffer,dupCountLNRefExists);
    if (dupCountLNRefExists) {
      dupCountLNRef.writeToLog(logBuffer);
    }
  }
  /** 
 * @see IN#readFromLog
 */
  public void readFromLog(  ByteBuffer itemBuffer,  byte entryTypeVersion) throws LogException {
    super.readFromLog(itemBuffer,entryTypeVersion);
    dupKey=LogUtils.readByteArray(itemBuffer);
    boolean dupCountLNRefExists=LogUtils.readBoolean(itemBuffer);
    if (dupCountLNRefExists) {
      dupCountLNRef.readFromLog(itemBuffer,entryTypeVersion);
    }
 else {
      dupCountLNRef=null;
    }
  }
  /** 
 * DINS need to dump their dup key
 */
  protected void dumpLogAdditional(  StringBuffer sb){
    super.dumpLogAdditional(sb);
    sb.append(Key.dumpString(dupKey,0));
    if (dupCountLNRef != null) {
      dupCountLNRef.dumpLog(sb,true);
    }
  }
  public String beginTag(){
    return BEGIN_TAG;
  }
  public String endTag(){
    return END_TAG;
  }
  /** 
 * For unit test support:
 * @return a string that dumps information about this DIN, without
 */
  public String dumpString(  int nSpaces,  boolean dumpTags){
    StringBuffer sb=new StringBuffer();
    if (dumpTags) {
      sb.append(TreeUtils.indent(nSpaces));
      sb.append(beginTag());
      sb.append('\n');
    }
    sb.append(TreeUtils.indent(nSpaces + 2));
    sb.append("<dupkey>");
    sb.append(dupKey == null ? "" : Key.dumpString(dupKey,0));
    sb.append("</dupkey>");
    sb.append('\n');
    if (dupCountLNRef == null) {
      sb.append(TreeUtils.indent(nSpaces + 2));
      sb.append("<dupCountLN/>");
    }
 else {
      sb.append(dupCountLNRef.dumpString(nSpaces + 4,true));
    }
    sb.append('\n');
    sb.append(super.dumpString(nSpaces,false));
    if (dumpTags) {
      sb.append(TreeUtils.indent(nSpaces));
      sb.append(endTag());
    }
    return sb.toString();
  }
  public String toString(){
    return dumpString(0,true);
  }
  public String shortClassName(){
    return "DIN";
  }
@MethodObject static class DIN_updateDupCountLN {
    DIN_updateDupCountLN(    DIN _this,    Node target){
      this._this=_this;
      this.target=target;
    }
    void execute(){
      _this.dupCountLNRef.setTarget(target);
    }
    protected DIN _this;
    protected Node target;
    protected long oldSize;
    protected long newSize;
  }
@MethodObject static class DIN_updateDupCountLNRefAndNullTarget {
    DIN_updateDupCountLNRefAndNullTarget(    DIN _this,    long newLsn){
      this._this=_this;
      this.newLsn=newLsn;
    }
    void execute(){
      _this.setDirty(true);
      this.hook614();
      _this.dupCountLNRef.setTarget(null);
      _this.dupCountLNRef.setLsn(newLsn);
    }
    protected DIN _this;
    protected long newLsn;
    protected long oldSize;
    protected long newSize;
    protected void hook614(){
    }
  }
}
