package com.sleepycat.je.latch;
public interface Latch {
  /** 
 * @return a LatchStats object with information about this latch.
 */
  public LatchStats getLatchStats();
}
