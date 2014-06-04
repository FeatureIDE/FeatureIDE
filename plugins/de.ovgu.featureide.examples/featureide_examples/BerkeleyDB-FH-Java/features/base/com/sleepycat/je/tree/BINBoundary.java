package com.sleepycat.je.tree;
import de.ovgu.cide.jakutil.*;
/** 
 * Contains information about the BIN returned by a search.
 */
public class BINBoundary {
  /** 
 * The last BIN was returned. 
 */
  public boolean isLastBin;
  /** 
 * The first BIN was returned. 
 */
  public boolean isFirstBin;
}
