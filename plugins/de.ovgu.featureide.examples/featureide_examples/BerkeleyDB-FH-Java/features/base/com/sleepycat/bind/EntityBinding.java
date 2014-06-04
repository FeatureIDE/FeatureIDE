package com.sleepycat.bind;
import com.sleepycat.je.DatabaseEntry;
import de.ovgu.cide.jakutil.*;
/** 
 * A binding between a key-value entry pair and an entity object.
 * @author Mark Hayes
 */
public interface EntityBinding {
  /** 
 * Converts key and data entry buffers into an entity Object.
 * @param keyis the source key entry.
 * @param datais the source data entry.
 * @return the resulting Object.
 */
  Object entryToObject(  DatabaseEntry key,  DatabaseEntry data);
  /** 
 * Extracts the key entry from an entity Object.
 * @param objectis the source Object.
 * @param keyis the destination entry buffer.
 */
  void objectToKey(  Object object,  DatabaseEntry key);
  /** 
 * Extracts the data entry from an entity Object.
 * @param objectis the source Object.
 * @param datais the destination entry buffer.
 */
  void objectToData(  Object object,  DatabaseEntry data);
}
