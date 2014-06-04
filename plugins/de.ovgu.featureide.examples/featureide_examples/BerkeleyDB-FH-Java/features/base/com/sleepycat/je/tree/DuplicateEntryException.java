package com.sleepycat.je.tree;
import com.sleepycat.je.DatabaseException;
import de.ovgu.cide.jakutil.*;
/** 
 * Exception to indicate that an entry is already present in a node.
 */
public class DuplicateEntryException extends DatabaseException {
  public DuplicateEntryException(){
    super();
  }
  public DuplicateEntryException(  String message){
    super(message);
  }
}
