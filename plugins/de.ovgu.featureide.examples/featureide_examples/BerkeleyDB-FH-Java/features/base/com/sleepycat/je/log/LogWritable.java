package com.sleepycat.je.log;
import java.nio.ByteBuffer;
import de.ovgu.cide.jakutil.*;
/** 
 * A class that implements LogWritable knows how to write itself into the JE
 * log.
 */
public interface LogWritable {
  /** 
 * @return number of bytes used to store this object.
 */
  public int getLogSize();
  /** 
 * Serialize this object into the buffer. 
 * @param logBuffer is the destination buffer
 */
  public void writeToLog(  ByteBuffer logBuffer);
}
