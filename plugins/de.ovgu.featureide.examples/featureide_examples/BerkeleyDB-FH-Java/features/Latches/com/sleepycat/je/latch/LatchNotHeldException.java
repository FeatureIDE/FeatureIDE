package com.sleepycat.je.latch;
import de.ovgu.cide.jakutil.*;
/** 
 * An exception that is thrown when a latch is not held but a method is invoked
 * on it that assumes it is held.
 */
public class LatchNotHeldException extends LatchException {
  public LatchNotHeldException(){
    super();
  }
  public LatchNotHeldException(  String message){
    super(message);
  }
}
