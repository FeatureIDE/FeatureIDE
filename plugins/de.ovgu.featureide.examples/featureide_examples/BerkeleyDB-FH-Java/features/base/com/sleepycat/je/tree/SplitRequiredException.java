package com.sleepycat.je.tree;
import de.ovgu.cide.jakutil.*;
/** 
 * Indicates that we need to return to the top of the tree in order to
 * do a forced splitting pass.
 */
class SplitRequiredException extends Exception {
  public SplitRequiredException(){
  }
}
