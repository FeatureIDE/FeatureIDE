package com.sleepycat.je;
import java.util.Set;
import de.ovgu.cide.jakutil.*;
/** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
public interface SecondaryMultiKeyCreator {
  /** 
 * Javadoc for this public method is generated via
 * the doc templates in the doc_src directory.
 */
  public void createSecondaryKeys(  SecondaryDatabase secondary,  DatabaseEntry key,  DatabaseEntry data,  Set results) throws DatabaseException ;
}
