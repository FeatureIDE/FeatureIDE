package com.sleepycat.je.utilint;
import com.sleepycat.je.DatabaseException;
import de.ovgu.cide.jakutil.*;
/** 
 * Some internal inconsistency exception.
 */
public class InternalException extends DatabaseException {
  public InternalException(){
    super();
  }
  public InternalException(  String message){
    super(message);
  }
}
