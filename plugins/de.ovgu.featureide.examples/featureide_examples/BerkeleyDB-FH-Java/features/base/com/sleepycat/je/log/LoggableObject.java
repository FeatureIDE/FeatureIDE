package com.sleepycat.je.log;
import com.sleepycat.je.DatabaseException;
import de.ovgu.cide.jakutil.*;
/** 
 * A class that implements LoggableObject can be stored as a JE log entry.
 */
public interface LoggableObject extends LogWritable {
  /** 
 * All objects that are reponsible for a generating a type of log entry
 * must implement this.
 * @return the type of log entry 
 */
  public LogEntryType getLogType();
  /** 
 * Do any processing we need to do after logging, while under the logging
 * latch.
 */
  public void postLogWork(  long justLoggedLsn) throws DatabaseException ;
  /** 
 * Return true if this item can be marshalled outside the log write
 * latch.
 */
  public boolean marshallOutsideWriteLatch();
  /** 
 * Returns true if this item should be counted as obsoleted when logged.
 * This currently applies to deleted LNs only.
 */
  public boolean countAsObsoleteWhenLogged();
}
