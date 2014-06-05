package com.sleepycat.je.tree;
import java.nio.ByteBuffer;
import java.util.ArrayList;
import java.util.List;
import com.sleepycat.je.DatabaseException;
import com.sleepycat.je.dbi.DatabaseId;
import com.sleepycat.je.dbi.DatabaseImpl;
import com.sleepycat.je.dbi.EnvironmentImpl;
import com.sleepycat.je.log.LogEntryType;
import com.sleepycat.je.log.LogException;
import com.sleepycat.je.log.LogReadable;
import com.sleepycat.je.log.LogUtils;
import com.sleepycat.je.log.LoggableObject;
import com.sleepycat.je.utilint.DbLsn;
import de.ovgu.cide.jakutil.*;
/** 
 * BINDelta contains the information needed to create a partial (delta) BIN log
 * entry. It also knows how to combine a full BIN log entry and a delta to
 * generate a new BIN.
 */
public class BINDelta implements LoggableObject, LogReadable {
  private DatabaseId dbId;
  private long lastFullLsn;
  private List deltas;
  private LogEntryType logEntryType;
  /** 
 * Read a BIN and create the deltas.
 */
  public BINDelta(  BIN bin){
    lastFullLsn=bin.getLastFullVersion();
    dbId=bin.getDatabaseId();
    deltas=new ArrayList();
    logEntryType=bin.getBINDeltaType();
    for (int i=0; i < bin.getNEntries(); i++) {
      if (bin.isDirty(i)) {
        deltas.add(new DeltaInfo(bin.getKey(i),bin.getLsn(i),bin.getState(i)));
      }
    }
  }
  /** 
 * For instantiating from the log.
 */
  public BINDelta(){
    dbId=new DatabaseId();
    lastFullLsn=DbLsn.NULL_LSN;
    deltas=new ArrayList();
  }
  /** 
 * @return a count of deltas for this BIN.
 */
  int getNumDeltas(){
    return deltas.size();
  }
  /** 
 * @return the dbId for this BIN.
 */
  public DatabaseId getDbId(){
    return dbId;
  }
  /** 
 * @return the last full version of this BIN
 */
  public long getLastFullLsn(){
    return lastFullLsn;
  }
  /** 
 * Create a BIN by starting with the full version and applying the deltas.
 */
  public BIN reconstituteBIN(  EnvironmentImpl env) throws DatabaseException {
    BIN fullBIN=(BIN)env.getLogManager().get(lastFullLsn);
    DatabaseImpl db=env.getDbMapTree().getDb(dbId);
    fullBIN.setDatabase(db);
    fullBIN.setLastFullLsn(lastFullLsn);
    this.hook612(fullBIN);
    for (int i=0; i < deltas.size(); i++) {
      DeltaInfo info=(DeltaInfo)deltas.get(i);
      int foundIndex=fullBIN.findEntry(info.getKey(),true,false);
      if (foundIndex >= 0 && (foundIndex & IN.EXACT_MATCH) != 0) {
        foundIndex&=~IN.EXACT_MATCH;
        if (info.isKnownDeleted()) {
          fullBIN.setKnownDeleted(foundIndex);
        }
 else {
          fullBIN.updateEntry(foundIndex,info.getLsn(),info.getState());
        }
      }
 else {
        if (!info.isKnownDeleted()) {
          ChildReference entry=new ChildReference(null,info.getKey(),info.getLsn(),info.getState());
          boolean insertOk=fullBIN.insertEntry(entry);
          assert insertOk;
        }
      }
    }
    fullBIN.setGeneration(0);
    this.hook611(fullBIN);
    return fullBIN;
  }
  public LogEntryType getLogType(){
    return logEntryType;
  }
  /** 
 * @see LoggableObject#marshallOutsideWriteLatchCan be marshalled outside the log write latch.
 */
  public boolean marshallOutsideWriteLatch(){
    return true;
  }
  /** 
 * @see LoggableObject#countAsObsoleteWhenLogged
 */
  public boolean countAsObsoleteWhenLogged(){
    return false;
  }
  public void postLogWork(  long justLoggedLsn){
  }
  public void readFromLog(  ByteBuffer itemBuffer,  byte entryTypeVersion) throws LogException {
    dbId.readFromLog(itemBuffer,entryTypeVersion);
    lastFullLsn=LogUtils.readLong(itemBuffer);
    int numDeltas=LogUtils.readInt(itemBuffer);
    for (int i=0; i < numDeltas; i++) {
      DeltaInfo info=new DeltaInfo();
      info.readFromLog(itemBuffer,entryTypeVersion);
      deltas.add(info);
    }
  }
  public int getLogSize(){
    int size=dbId.getLogSize() + LogUtils.LONG_BYTES + LogUtils.INT_BYTES;
    for (int i=0; i < deltas.size(); i++) {
      DeltaInfo info=(DeltaInfo)deltas.get(i);
      size+=info.getLogSize();
    }
    return size;
  }
  public void writeToLog(  ByteBuffer logBuffer){
    dbId.writeToLog(logBuffer);
    LogUtils.writeLong(logBuffer,lastFullLsn);
    LogUtils.writeInt(logBuffer,deltas.size());
    for (int i=0; i < deltas.size(); i++) {
      DeltaInfo info=(DeltaInfo)deltas.get(i);
      info.writeToLog(logBuffer);
    }
  }
  public void dumpLog(  StringBuffer sb,  boolean verbose){
    dbId.dumpLog(sb,verbose);
    sb.append("<lastFullLsn>");
    sb.append(DbLsn.toString(lastFullLsn));
    sb.append("</lastFullLsn>");
    sb.append("<deltas size=\"").append(deltas.size()).append("\"/>");
    for (int i=0; i < deltas.size(); i++) {
      DeltaInfo info=(DeltaInfo)deltas.get(i);
      info.dumpLog(sb,verbose);
    }
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
  protected void hook611(  BIN fullBIN) throws DatabaseException {
  }
  protected void hook612(  BIN fullBIN) throws DatabaseException {
  }
}
