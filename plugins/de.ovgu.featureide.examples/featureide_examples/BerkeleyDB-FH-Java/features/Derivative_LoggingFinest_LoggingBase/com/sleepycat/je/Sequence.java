package com.sleepycat.je;
public class Sequence {
  protected void hook82(  boolean cached,  boolean wrapped,  long retVal) throws DatabaseException {
    if (logger.isLoggable(Level.FINEST)) {
      logger.log(Level.FINEST,"Sequence.get" + " value=" + retVal + " cached="+ cached+ " wrapped="+ wrapped);
    }
    original(cached,wrapped,retVal);
  }
}
