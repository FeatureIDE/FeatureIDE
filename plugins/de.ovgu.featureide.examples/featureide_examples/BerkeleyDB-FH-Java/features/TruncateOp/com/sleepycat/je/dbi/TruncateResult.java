package com.sleepycat.je.dbi;
import de.ovgu.cide.jakutil.*;
/** 
 * Holds the result of a database truncate operation.
 */
public class TruncateResult {
  private DatabaseImpl db;
  private int count;
  TruncateResult(  DatabaseImpl db,  int count){
    this.db=db;
    this.count=count;
  }
  public DatabaseImpl getDatabase(){
    return db;
  }
  public int getRecordCount(){
    return count;
  }
}
