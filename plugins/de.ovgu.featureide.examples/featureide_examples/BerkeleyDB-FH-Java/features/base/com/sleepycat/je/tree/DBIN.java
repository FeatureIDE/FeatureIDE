package com.sleepycat.je.tree;
import java.nio.ByteBuffer;
import java.util.Comparator;
import com.sleepycat.je.DatabaseException;
import com.sleepycat.je.dbi.CursorImpl;
import com.sleepycat.je.dbi.DatabaseId;
import com.sleepycat.je.dbi.DatabaseImpl;
import com.sleepycat.je.dbi.DbConfigManager;
import com.sleepycat.je.dbi.MemoryBudget;
import com.sleepycat.je.log.LogEntryType;
import com.sleepycat.je.log.LogException;
import com.sleepycat.je.log.LogUtils;
import com.sleepycat.je.log.LoggableObject;
import de.ovgu.cide.jakutil.*;
/** 
 * A DBIN represents an Duplicate Bottom Internal Node in the JE tree.
 */
public final class DBIN extends BIN implements LoggableObject {
  private static final String BEGIN_TAG="<dbin>";
  private static final String END_TAG="</dbin>";
  /** 
 * Full key for this set of duplicates.
 */
  private byte[] dupKey;
  public DBIN(){
    super();
  }
  public DBIN(  DatabaseImpl db,  byte[] identifierKey,  int maxEntriesPerNode,  byte[] dupKey,  int level){
    super(db,identifierKey,maxEntriesPerNode,level);
    this.dupKey=dupKey;
  }
  /** 
 * Create a new DBIN. Need this because we can't call newInstance() without
 * getting a 0 node.
 */
  protected IN createNewInstance(  byte[] identifierKey,  int maxEntries,  int level){
    return new DBIN(getDatabase(),identifierKey,maxEntries,dupKey,level);
  }
  protected int generateLevel(  DatabaseId dbId,  int newLevel){
    return newLevel;
  }
  /** 
 * Return the comparator function to be used for DBINs. This is the user
 * defined duplicate comparison function, if defined.
 */
  public final Comparator getKeyComparator(){
    return getDatabase().getDuplicateComparator();
  }
  /** 
 * Return the key for this duplicate set.
 */
  public byte[] getDupKey(){
    return dupKey;
  }
  /** 
 * Get the key (dupe or identifier) in child that is used to locate it in
 * 'this' node.
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
  /** 
 * @return true if this node is a duplicate-bearing node type, false if
 * otherwise.
 */
  public boolean containsDuplicates(){
    return true;
  }
  /** 
 * @return the log entry type to use for bin delta log entries.
 */
  LogEntryType getBINDeltaType(){
    return LogEntryType.LOG_DUP_BIN_DELTA;
  }
  public BINReference createReference(){
    return new DBINReference(getNodeId(),getDatabase().getId(),getIdentifierKey(),dupKey);
  }
  protected boolean canBeAncestor(  boolean targetContainsDuplicates){
    return false;
  }
  /** 
 * @Override
 */
  boolean hasNonLNChildren(){
    return false;
  }
  /** 
 * The following four methods access the correct fields in a cursor
 * depending on whether "this" is a BIN or DBIN. For BIN's, the
 * CursorImpl.index and CursorImpl.bin fields should be used. For DBIN's,
 * the CursorImpl.dupIndex and CursorImpl.dupBin fields should be used.
 */
  BIN getCursorBIN(  CursorImpl cursor){
    return cursor.getDupBIN();
  }
  BIN getCursorBINToBeRemoved(  CursorImpl cursor){
    return cursor.getDupBINToBeRemoved();
  }
  int getCursorIndex(  CursorImpl cursor){
    return cursor.getDupIndex();
  }
  void setCursorBIN(  CursorImpl cursor,  BIN bin){
    cursor.setDupBIN((DBIN)bin);
  }
  void setCursorIndex(  CursorImpl cursor,  int index){
    cursor.setDupIndex(index);
  }
  boolean matchLNByNodeId(  TreeLocation location,  long nodeId) throws DatabaseException {
    for (int i=0; i < getNEntries(); i++) {
      LN ln=(LN)fetchTarget(i);
      if (ln != null) {
        if (ln.getNodeId() == nodeId) {
          location.bin=this;
          location.index=i;
          location.lnKey=getKey(i);
          location.childLsn=getLsn(i);
          return true;
        }
      }
    }
    return false;
  }
  void accumulateStats(  TreeWalkerStatsAccumulator acc){
    acc.processDBIN(this,new Long(getNodeId()),getLevel());
  }
  public String beginTag(){
    return BEGIN_TAG;
  }
  public String endTag(){
    return END_TAG;
  }
  /** 
 * For unit test support:
 * @return a string that dumps information about this IN, without
 */
  public String dumpString(  int nSpaces,  boolean dumpTags){
    StringBuffer sb=new StringBuffer();
    sb.append(TreeUtils.indent(nSpaces));
    sb.append(beginTag());
    sb.append('\n');
    sb.append(TreeUtils.indent(nSpaces + 2));
    sb.append("<dupkey>");
    sb.append(dupKey == null ? "" : Key.dumpString(dupKey,0));
    sb.append("</dupkey>");
    sb.append('\n');
    sb.append(super.dumpString(nSpaces,false));
    sb.append(TreeUtils.indent(nSpaces));
    sb.append(endTag());
    return sb.toString();
  }
  /** 
 * @see LoggableObject#getLogType
 */
  public LogEntryType getLogType(){
    return LogEntryType.LOG_DBIN;
  }
  /** 
 * @see LoggableObject#getLogSize
 */
  public int getLogSize(){
    int size=super.getLogSize();
    size+=LogUtils.getByteArrayLogSize(dupKey);
    return size;
  }
  /** 
 * @see LoggableObject#writeToLog
 */
  public void writeToLog(  ByteBuffer logBuffer){
    super.writeToLog(logBuffer);
    LogUtils.writeByteArray(logBuffer,dupKey);
  }
  /** 
 * @see BIN#readFromLog
 */
  public void readFromLog(  ByteBuffer itemBuffer,  byte entryTypeVersion) throws LogException {
    super.readFromLog(itemBuffer,entryTypeVersion);
    dupKey=LogUtils.readByteArray(itemBuffer);
  }
  /** 
 * DBINS need to dump their dup key
 */
  protected void dumpLogAdditional(  StringBuffer sb){
    super.dumpLogAdditional(sb);
    sb.append(Key.dumpString(dupKey,0));
  }
  public String shortClassName(){
    return "DBIN";
  }
}
