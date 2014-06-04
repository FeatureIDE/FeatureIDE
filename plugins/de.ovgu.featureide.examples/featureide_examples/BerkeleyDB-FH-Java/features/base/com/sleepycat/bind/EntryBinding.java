package com.sleepycat.bind;
import com.sleepycat.je.DatabaseEntry;
import de.ovgu.cide.jakutil.*;
/** 
 * A binding between a key or data entry and a key or data object.
 * @author Mark Hayes
 */
public interface EntryBinding {
  /** 
 * Converts a entry buffer into an Object.
 * @param entryis the source entry buffer.
 * @return the resulting Object.
 */
  Object entryToObject(  DatabaseEntry entry);
  /** 
 * Converts an Object into a entry buffer.
 * @param objectis the source Object.
 * @param entryis the destination entry buffer.
 */
  void objectToEntry(  Object object,  DatabaseEntry entry);
}
