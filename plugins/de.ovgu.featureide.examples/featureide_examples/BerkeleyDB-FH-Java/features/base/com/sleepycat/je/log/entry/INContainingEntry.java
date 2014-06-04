package com.sleepycat.je.log.entry;
import com.sleepycat.je.DatabaseException;
import com.sleepycat.je.dbi.DatabaseId;
import com.sleepycat.je.dbi.EnvironmentImpl;
import com.sleepycat.je.tree.IN;
import de.ovgu.cide.jakutil.*;
/** 
 * An INContainingEntry is a log entry that contains internal nodes.
 */
public interface INContainingEntry {
  /** 
 * @return the IN held within this log entry.
 */
  public IN getIN(  EnvironmentImpl env) throws DatabaseException ;
  /** 
 * @return the database id held within this log entry.
 */
  public DatabaseId getDbId();
  /** 
 * @return the LSN that represents this IN.
 */
  public long getLsnOfIN(  long lastReadLsn);
}
