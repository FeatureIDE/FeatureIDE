package com.sleepycat.je.tree;
import java.nio.ByteBuffer;
import com.sleepycat.je.dbi.DatabaseId;
import com.sleepycat.je.log.LogEntryType;
import com.sleepycat.je.log.LogException;
import com.sleepycat.je.log.LogUtils;
import de.ovgu.cide.jakutil.*;
/** 
 * A NameLN represents a Leaf Node in the name->database id mapping tree.
 */
public final class NameLN extends LN {
  private static final String BEGIN_TAG="<nameLN>";
  private static final String END_TAG="</nameLN>";
  private DatabaseId id;
  private boolean deleted;
  /** 
 * In the ideal world, we'd have a base LN class so that this NameLN
 * doesn't have a superfluous data field, but we want to optimize the LN
 * class for size and speed right now.
 */
  public NameLN(  DatabaseId id){
    super(new byte[0]);
    this.id=id;
    deleted=false;
  }
  /** 
 * Create an empty NameLN, to be filled in from the log.
 */
  public NameLN(){
    super();
    id=new DatabaseId();
  }
  public boolean isDeleted(){
    return deleted;
  }
  void makeDeleted(){
    deleted=true;
  }
  public DatabaseId getId(){
    return id;
  }
  public void setId(  DatabaseId id){
    this.id=id;
  }
  public String toString(){
    return dumpString(0,true);
  }
  public String beginTag(){
    return BEGIN_TAG;
  }
  public String endTag(){
    return END_TAG;
  }
  public String dumpString(  int nSpaces,  boolean dumpTags){
    StringBuffer sb=new StringBuffer();
    sb.append(super.dumpString(nSpaces,dumpTags));
    sb.append('\n');
    sb.append(TreeUtils.indent(nSpaces));
    sb.append("<deleted val=\"").append(Boolean.toString(deleted));
    sb.append("\">");
    sb.append('\n');
    sb.append(TreeUtils.indent(nSpaces));
    sb.append("<id val=\"").append(id);
    sb.append("\">");
    sb.append('\n');
    return sb.toString();
  }
  /** 
 * Log type for transactional entries.
 */
  protected LogEntryType getTransactionalLogType(){
    return LogEntryType.LOG_NAMELN_TRANSACTIONAL;
  }
  /** 
 * @see LN#getLogType
 */
  public LogEntryType getLogType(){
    return LogEntryType.LOG_NAMELN;
  }
  /** 
 * @see LN#getLogSize
 */
  public int getLogSize(){
    return super.getLogSize() + id.getLogSize() + LogUtils.getBooleanLogSize();
  }
  /** 
 * @see LN#writeToLog
 */
  public void writeToLog(  ByteBuffer logBuffer){
    super.writeToLog(logBuffer);
    id.writeToLog(logBuffer);
    LogUtils.writeBoolean(logBuffer,deleted);
  }
  /** 
 * @see LN#readFromLog
 */
  public void readFromLog(  ByteBuffer itemBuffer,  byte entryTypeVersion) throws LogException {
    super.readFromLog(itemBuffer,entryTypeVersion);
    id.readFromLog(itemBuffer,entryTypeVersion);
    deleted=LogUtils.readBoolean(itemBuffer);
  }
  /** 
 * Dump additional fields. Done this way so the additional info can be
 * within the XML tags defining the dumped log entry.
 */
  protected void dumpLogAdditional(  StringBuffer sb,  boolean verbose){
    id.dumpLog(sb,true);
  }
}
