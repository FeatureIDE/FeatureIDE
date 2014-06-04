package com.sleepycat.je.log;
import java.io.IOException;
import java.nio.ByteBuffer;
import com.sleepycat.je.DatabaseException;
import com.sleepycat.je.dbi.EnvironmentImpl;
import com.sleepycat.je.log.entry.LogEntry;
import com.sleepycat.je.utilint.DbLsn;
import de.ovgu.cide.jakutil.*;
/** 
 * SearchFileReader searches for the a given entry type.
 */
public class SearchFileReader extends FileReader {
  private LogEntryType targetType;
  private LogEntry logEntry;
  /** 
 * Create this reader to start at a given LSN.
 */
  public SearchFileReader(  EnvironmentImpl env,  int readBufferSize,  boolean forward,  long startLsn,  long endOfFileLsn,  LogEntryType targetType) throws IOException, DatabaseException {
    super(env,readBufferSize,forward,startLsn,null,endOfFileLsn,DbLsn.NULL_LSN);
    this.targetType=targetType;
    logEntry=targetType.getNewLogEntry();
  }
  /** 
 * @return true if this is a targetted entry.
 */
  protected boolean isTargetEntry(  byte logEntryTypeNumber,  byte logEntryTypeVersion){
    return (targetType.equalsType(logEntryTypeNumber,logEntryTypeVersion));
  }
  /** 
 * This reader instantiate the first object of a given log entry.
 */
  protected boolean processEntry(  ByteBuffer entryBuffer) throws DatabaseException {
    logEntry.readEntry(entryBuffer,currentEntrySize,currentEntryTypeVersion,true);
    return true;
  }
  /** 
 * @return the last object read.
 */
  public Object getLastObject(){
    return logEntry.getMainItem();
  }
}
