package com.sleepycat.je.tree;
import de.ovgu.cide.jakutil.*;
/** 
 * Contains the result of a tree search
 */
public class SearchResult {
  public boolean exactParentFound;
  public boolean keepSearching;
  public boolean childNotResident;
  public IN parent;
  public int index;
  public SearchResult(){
    exactParentFound=false;
    keepSearching=true;
    parent=null;
    index=-1;
    childNotResident=false;
  }
  public String toString(){
    return "exactParentFound=" + exactParentFound + " keepSearching="+ keepSearching+ " parent="+ ((parent == null) ? "null" : Long.toString(parent.getNodeId()))+ " index="+ index+ " childNotResident="+ childNotResident;
  }
}
