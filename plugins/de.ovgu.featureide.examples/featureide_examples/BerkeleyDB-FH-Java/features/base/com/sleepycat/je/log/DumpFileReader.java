package com.sleepycat.je.log;
import java.io.IOException;
import java.util.HashSet;
import java.util.Set;
import java.util.StringTokenizer;
import com.sleepycat.je.DatabaseException;
import com.sleepycat.je.dbi.EnvironmentImpl;
import com.sleepycat.je.utilint.DbLsn;
import de.ovgu.cide.jakutil.*;
/** 
 * The DumpFileReader prints every log entry to stdout.
 */
public abstract class DumpFileReader extends FileReader {
  private Set targetEntryTypes;
  protected Set targetTxnIds;
  protected boolean verbose;
  /** 
 * Create this reader to start at a given LSN.
 */
  public DumpFileReader(  EnvironmentImpl env,  int readBufferSize,  long startLsn,  long finishLsn,  String entryTypes,  String txnIds,  boolean verbose) throws IOException, DatabaseException {
    super(env,readBufferSize,true,startLsn,null,DbLsn.NULL_LSN,finishLsn);
    targetEntryTypes=new HashSet();
    if (entryTypes != null) {
      StringTokenizer tokenizer=new StringTokenizer(entryTypes,",");
      while (tokenizer.hasMoreTokens()) {
        String typeString=(String)tokenizer.nextToken();
        targetEntryTypes.add(new Byte(typeString.trim()));
      }
    }
    targetTxnIds=new HashSet();
    if (txnIds != null) {
      StringTokenizer tokenizer=new StringTokenizer(txnIds,",");
      while (tokenizer.hasMoreTokens()) {
        String txnIdString=(String)tokenizer.nextToken();
        targetTxnIds.add(new Long(txnIdString.trim()));
      }
    }
    this.verbose=verbose;
  }
  /** 
 * @return true if this reader should process this entry, or just
 * skip over it.
 */
  protected boolean isTargetEntry(  byte logEntryTypeNumber,  byte logEntryTypeVersion){
    if (targetEntryTypes.size() == 0) {
      return true;
    }
 else {
      return targetEntryTypes.contains(new Byte(logEntryTypeNumber));
    }
  }
  public void summarize(){
  }
}
