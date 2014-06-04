package com.sleepycat.je.log;
import de.ovgu.cide.jakutil.*;
/** 
 * Log file doesn't exist.
 */
public class LogFileNotFoundException extends LogException {
  public LogFileNotFoundException(  String message){
    super(message);
  }
}
