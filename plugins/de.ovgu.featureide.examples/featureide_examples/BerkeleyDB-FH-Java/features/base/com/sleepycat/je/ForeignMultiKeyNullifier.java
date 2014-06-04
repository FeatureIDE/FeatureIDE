package com.sleepycat.je;
import de.ovgu.cide.jakutil.*;
/** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
public interface ForeignMultiKeyNullifier {
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public boolean nullifyForeignKey(  SecondaryDatabase secondary,  DatabaseEntry key,  DatabaseEntry data,  DatabaseEntry secKey) throws DatabaseException ;
}
