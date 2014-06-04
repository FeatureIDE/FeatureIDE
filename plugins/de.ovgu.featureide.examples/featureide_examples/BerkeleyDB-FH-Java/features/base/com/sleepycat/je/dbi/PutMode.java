package com.sleepycat.je.dbi;
import de.ovgu.cide.jakutil.*;
/** 
 * Internal class used to distinguish which variety of putXXX() that
 * Cursor.putInternal() should use.
 */
public class PutMode {
  public static final PutMode NODUP=new PutMode();
  public static final PutMode CURRENT=new PutMode();
  public static final PutMode OVERWRITE=new PutMode();
  public static final PutMode NOOVERWRITE=new PutMode();
}
