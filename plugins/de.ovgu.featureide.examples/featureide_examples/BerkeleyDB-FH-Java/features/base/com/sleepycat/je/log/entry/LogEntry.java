package com.sleepycat.je.log.entry;
import java.nio.ByteBuffer;
import com.sleepycat.je.DatabaseException;
import de.ovgu.cide.jakutil.*;
/** 
 * A Log entry allows you to read, write and dump a database log entry.  Each
 * entry may be made up of one or more loggable items.
 */
public interface LogEntry extends Cloneable {
  /** 
 * Read in an log entry.
 */
  void readEntry(  ByteBuffer entryBuffer,  int entrySize,  byte entryTypeVersion,  boolean readFullItem) throws DatabaseException ;
  /** 
 * Print out the contents of an entry.
 */
  StringBuffer dumpEntry(  StringBuffer sb,  boolean verbose);
  /** 
 * @return the first item of the log entry
 */
  Object getMainItem();
  /** 
 * @return a shallow clone.
 */
  public Object clone() throws CloneNotSupportedException ;
  /** 
 * @return true if the LogEntry is a transactional log entry type.
 */
  public boolean isTransactional();
  /** 
 * @return return the transaction id if this log entry is transactional,
 * 0 otherwise.
 */
  public long getTransactionId();
}
