package com.sleepycat.je.log;
import java.util.HashSet;
import java.util.Set;
import com.sleepycat.je.DatabaseException;
import com.sleepycat.je.log.entry.BINDeltaLogEntry;
import com.sleepycat.je.log.entry.DeletedDupLNLogEntry;
import com.sleepycat.je.log.entry.INLogEntry;
import com.sleepycat.je.log.entry.LNLogEntry;
import com.sleepycat.je.log.entry.LogEntry;
import com.sleepycat.je.log.entry.SingleItemLogEntry;
import de.ovgu.cide.jakutil.*;
/** 
 * LogEntryType is a type safe enumeration of all log entry types. 
 * <p>When adding a new version of a log entry, make sure the owning Loggable
 * object is capable of reading in older versions from the log. The Loggable
 * object must be sure that older versions are converted in memory into a
 * correct instance of the newest version, so when that Loggable object is
 * written again as the result of migration, eviction, the resulting new log
 * entry conforms to the requirements of the new version.  If context objects
 * are required for data conversion, the conversion can be done in the
 * Node.postFetchInit method.</p>
 */
public class LogEntryType {
  private static final int MAX_TYPE_NUM=27;
  private static LogEntryType[] LOG_TYPES=new LogEntryType[MAX_TYPE_NUM];
  public static final LogEntryType LOG_LN_TRANSACTIONAL=new LogEntryType((byte)1,(byte)0,"LN_TX",new LNLogEntry(com.sleepycat.je.tree.LN.class,true));
  public static final LogEntryType LOG_LN=new LogEntryType((byte)2,(byte)0,"LN",new LNLogEntry(com.sleepycat.je.tree.LN.class,false));
  public static final LogEntryType LOG_MAPLN_TRANSACTIONAL=new LogEntryType((byte)3,(byte)1,"MapLN_TX",new LNLogEntry(com.sleepycat.je.tree.MapLN.class,true));
  public static final LogEntryType LOG_MAPLN=new LogEntryType((byte)4,(byte)1,"MapLN",new LNLogEntry(com.sleepycat.je.tree.MapLN.class,false));
  public static final LogEntryType LOG_NAMELN_TRANSACTIONAL=new LogEntryType((byte)5,(byte)0,"NameLN_TX",new LNLogEntry(com.sleepycat.je.tree.NameLN.class,true));
  public static final LogEntryType LOG_NAMELN=new LogEntryType((byte)6,(byte)0,"NameLN",new LNLogEntry(com.sleepycat.je.tree.NameLN.class,false));
  public static final LogEntryType LOG_DEL_DUPLN_TRANSACTIONAL=new LogEntryType((byte)7,(byte)0,"DelDupLN_TX",new DeletedDupLNLogEntry(true));
  public static final LogEntryType LOG_DEL_DUPLN=new LogEntryType((byte)8,(byte)0,"DelDupLN",new DeletedDupLNLogEntry(false));
  public static final LogEntryType LOG_DUPCOUNTLN_TRANSACTIONAL=new LogEntryType((byte)9,(byte)0,"DupCountLN_TX",new LNLogEntry(com.sleepycat.je.tree.DupCountLN.class,true));
  public static final LogEntryType LOG_DUPCOUNTLN=new LogEntryType((byte)10,(byte)0,"DupCountLN",new LNLogEntry(com.sleepycat.je.tree.DupCountLN.class,false));
  public static final LogEntryType LOG_FILESUMMARYLN=new LogEntryType((byte)11,(byte)2,"FileSummaryLN",new LNLogEntry(com.sleepycat.je.tree.FileSummaryLN.class,false));
  public static final LogEntryType LOG_IN=new LogEntryType((byte)12,(byte)2,"IN",new INLogEntry(com.sleepycat.je.tree.IN.class));
  public static final LogEntryType LOG_BIN=new LogEntryType((byte)13,(byte)2,"BIN",new INLogEntry(com.sleepycat.je.tree.BIN.class));
  public static final LogEntryType LOG_DIN=new LogEntryType((byte)14,(byte)2,"DIN",new INLogEntry(com.sleepycat.je.tree.DIN.class));
  public static final LogEntryType LOG_DBIN=new LogEntryType((byte)15,(byte)2,"DBIN",new INLogEntry(com.sleepycat.je.tree.DBIN.class));
  public static final LogEntryType[] IN_TYPES={LogEntryType.LOG_IN,LogEntryType.LOG_BIN,LogEntryType.LOG_DIN,LogEntryType.LOG_DBIN};
  /** 
 * If you add new types, be sure to update MAX_TYPE_NUM at the top.**
 */
  private static final int MAX_NODE_TYPE_NUM=15;
  public static boolean isNodeType(  byte typeNum,  byte version){
    return (typeNum <= MAX_NODE_TYPE_NUM);
  }
  public static final LogEntryType LOG_ROOT=new LogEntryType((byte)16,(byte)1,"Root",new SingleItemLogEntry(com.sleepycat.je.dbi.DbTree.class));
  public static final LogEntryType LOG_TXN_COMMIT=new LogEntryType((byte)17,(byte)0,"Commit",new SingleItemLogEntry(com.sleepycat.je.txn.TxnCommit.class));
  public static final LogEntryType LOG_TXN_ABORT=new LogEntryType((byte)18,(byte)0,"Abort",new SingleItemLogEntry(com.sleepycat.je.txn.TxnAbort.class));
  public static final LogEntryType LOG_CKPT_START=new LogEntryType((byte)19,(byte)0,"CkptStart",new SingleItemLogEntry(com.sleepycat.je.recovery.CheckpointStart.class));
  public static final LogEntryType LOG_CKPT_END=new LogEntryType((byte)20,(byte)0,"CkptEnd",new SingleItemLogEntry(com.sleepycat.je.recovery.CheckpointEnd.class));
  public static final LogEntryType LOG_IN_DELETE_INFO=new LogEntryType((byte)21,(byte)0,"INDelete",new SingleItemLogEntry(com.sleepycat.je.tree.INDeleteInfo.class));
  public static final LogEntryType LOG_BIN_DELTA=new LogEntryType((byte)22,(byte)0,"BINDelta",new BINDeltaLogEntry(com.sleepycat.je.tree.BINDelta.class));
  public static final LogEntryType LOG_DUP_BIN_DELTA=new LogEntryType((byte)23,(byte)0,"DupBINDelta",new BINDeltaLogEntry(com.sleepycat.je.tree.BINDelta.class));
  public static final LogEntryType LOG_TRACE=new LogEntryType((byte)24,(byte)0,"Trace",new SingleItemLogEntry(com.sleepycat.je.utilint.Tracer.class));
  public static final LogEntryType LOG_FILE_HEADER=new LogEntryType((byte)25,(byte)0,"FileHeader",new SingleItemLogEntry(com.sleepycat.je.log.FileHeader.class));
  public static final LogEntryType LOG_IN_DUPDELETE_INFO=new LogEntryType((byte)26,(byte)0,"INDupDelete",new SingleItemLogEntry(com.sleepycat.je.tree.INDupDeleteInfo.class));
  public static final LogEntryType LOG_TXN_PREPARE=new LogEntryType((byte)27,(byte)0,"Prepare",new SingleItemLogEntry(com.sleepycat.je.txn.TxnPrepare.class));
  /** 
 * If you add new types, be sure to update MAX_TYPE_NUM at the top.**
 */
  private static final byte PROVISIONAL_MASK=(byte)0x80;
  private static final byte IGNORE_PROVISIONAL=~PROVISIONAL_MASK;
  private byte typeNum;
  private byte version;
  private String displayName;
  private LogEntry logEntry;
  /** 
 * For base class support.
 */
  LogEntryType(  byte typeNum,  byte version){
    this.typeNum=typeNum;
    this.version=version;
  }
  /** 
 * Create the static log types.
 */
  private LogEntryType(  byte typeNum,  byte version,  String displayName,  LogEntry logEntry){
    this.typeNum=typeNum;
    this.version=version;
    this.logEntry=logEntry;
    this.displayName=displayName;
    LOG_TYPES[typeNum - 1]=this;
  }
  public boolean isNodeType(){
    return (typeNum <= MAX_NODE_TYPE_NUM);
  }
  /** 
 * @return the static version of this type
 */
  public static LogEntryType findType(  byte typeNum,  byte version){
    if (typeNum <= 0 || typeNum > MAX_TYPE_NUM) {
      return null;
    }
    return (LogEntryType)LOG_TYPES[typeNum - 1];
  }
  /** 
 * Get a copy of all types for unit testing.
 */
  public static Set getAllTypes(){
    HashSet ret=new HashSet();
    for (int i=0; i < MAX_TYPE_NUM; i++) {
      ret.add(LOG_TYPES[i]);
    }
    return ret;
  }
  /** 
 * @return the log entry type owned by the shared, static version
 */
  public LogEntry getSharedLogEntry(){
    return logEntry;
  }
  /** 
 * @return a clone of the log entry type for a given log type.
 */
  LogEntry getNewLogEntry() throws DatabaseException {
    try {
      return (LogEntry)logEntry.clone();
    }
 catch (    CloneNotSupportedException e) {
      throw new DatabaseException(e);
    }
  }
  /** 
 * Set the provisional bit.
 */
  static byte setProvisional(  byte version){
    return (byte)(version | PROVISIONAL_MASK);
  }
  /** 
 * Clear the provisional bit.
 */
  public static byte clearProvisional(  byte version){
    return (byte)(version & IGNORE_PROVISIONAL);
  }
  /** 
 * @return true if the provisional bit is set.
 */
  static boolean isProvisional(  byte version){
    return ((version & PROVISIONAL_MASK) != 0);
  }
  byte getTypeNum(){
    return typeNum;
  }
  byte getVersion(){
    return version;
  }
  /** 
 * @return true if type number is valid.
 */
  static boolean isValidType(  byte typeNum){
    return typeNum > 0 && typeNum <= MAX_TYPE_NUM;
  }
  public String toString(){
    return displayName + "/" + version;
  }
  /** 
 * Check for equality without making a new object.
 */
  boolean equalsType(  byte typeNum,  byte version){
    return (this.typeNum == typeNum);
  }
  public boolean equalsType(  byte typeNum){
    return (this.typeNum == typeNum);
  }
  public boolean equals(  Object obj){
    if (this == obj) {
      return true;
    }
    if (!(obj instanceof LogEntryType)) {
      return false;
    }
    return typeNum == ((LogEntryType)obj).typeNum;
  }
  /** 
 * This is used as a hash key.
 */
  public int hashCode(){
    return typeNum;
  }
}
