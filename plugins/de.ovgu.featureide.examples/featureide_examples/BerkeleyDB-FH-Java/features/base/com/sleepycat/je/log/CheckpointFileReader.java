package com.sleepycat.je.log;
import java.io.IOException;
import java.nio.ByteBuffer;
import com.sleepycat.je.DatabaseException;
import com.sleepycat.je.dbi.EnvironmentImpl;
import de.ovgu.cide.jakutil.*;
/** 
 * CheckpointFileReader searches for root and checkpoint entries.
 */
public class CheckpointFileReader extends FileReader {
  private boolean isRoot;
  private boolean isCheckpointEnd;
  private boolean isCheckpointStart;
  /** 
 * Create this reader to start at a given LSN.
 */
  public CheckpointFileReader(  EnvironmentImpl env,  int readBufferSize,  boolean forward,  long startLsn,  long finishLsn,  long endOfFileLsn) throws IOException, DatabaseException {
    super(env,readBufferSize,forward,startLsn,null,endOfFileLsn,finishLsn);
  }
  /** 
 * @return true if this is a targetted entry.
 */
  protected boolean isTargetEntry(  byte logEntryTypeNumber,  byte logEntryTypeVersion){
    boolean isTarget=false;
    isRoot=false;
    isCheckpointEnd=false;
    isCheckpointStart=false;
    if (LogEntryType.LOG_CKPT_END.equalsType(logEntryTypeNumber,logEntryTypeVersion)) {
      isTarget=true;
      isCheckpointEnd=true;
    }
 else     if (LogEntryType.LOG_CKPT_START.equalsType(logEntryTypeNumber,logEntryTypeVersion)) {
      isTarget=true;
      isCheckpointStart=true;
    }
 else     if (LogEntryType.LOG_ROOT.equalsType(logEntryTypeNumber,logEntryTypeVersion)) {
      isTarget=true;
      isRoot=true;
    }
    return isTarget;
  }
  /** 
 * This reader instantiate the first object of a given log entry
 */
  protected boolean processEntry(  ByteBuffer entryBuffer) throws DatabaseException {
    return true;
  }
  /** 
 * @return true if last entry was a root entry.
 */
  public boolean isRoot(){
    return isRoot;
  }
  /** 
 * @return true if last entry was a checkpoint end entry.
 */
  public boolean isCheckpointEnd(){
    return isCheckpointEnd;
  }
  /** 
 * @return true if last entry was a checkpoint start entry.
 */
  public boolean isCheckpointStart(){
    return isCheckpointStart;
  }
}
