package com.sleepycat.je.latch;
import java.io.Serializable;
import de.ovgu.cide.jakutil.*;
/** 
 * A class that provides interesting stats about a particular latch.
 */
public class LatchStats implements Cloneable, Serializable {
  public int nAcquiresNoWaiters=0;
  /** 
 * Number of times acquire() was called when the latch was already owned by
 * the caller.
 */
  public int nAcquiresSelfOwned=0;
  /** 
 * Number of times acquire() was called with allowNesting=true when the
 * latch was already owned by the caller for shared access.
 */
  public int nAcquiresUpgrade=0;
  /** 
 * Number of times acquire() was called when the latch was already owned by
 * the some other thread.
 */
  public int nAcquiresWithContention=0;
  /** 
 * Number of times acquireNoWait() was called when the latch was
 * successfully acquired.
 */
  public int nAcquireNoWaitSuccessful=0;
  /** 
 * Number of unsuccessful acquireNoWait() calls.
 */
  public int nAcquireNoWaitUnsuccessful=0;
  /** 
 * Number of times acquireShared() was called when the latch was
 * successfully acquired.
 */
  public int nAcquireSharedSuccessful=0;
  /** 
 * Numbed of calls to release();
 */
  public int nReleases=0;
  public String toString(){
    StringBuffer sb=new StringBuffer();
    sb.append("nAcquiresNoWaiters=").append(nAcquiresNoWaiters).append('\n');
    sb.append("nAcquiresSelfOwned=").append(nAcquiresSelfOwned).append('\n');
    sb.append("nAcquiresUpgrade=").append(nAcquiresUpgrade).append('\n');
    sb.append("nAcquiresWithContention=").append(nAcquiresWithContention).append('\n');
    sb.append("nAcquiresNoWaitSuccessful=").append(nAcquireNoWaitSuccessful).append('\n');
    sb.append("nAcquiresNoWaitUnSuccessful=").append(nAcquireNoWaitUnsuccessful).append('\n');
    sb.append("nAcquiresSharedSuccessful=").append(nAcquireSharedSuccessful).append('\n');
    return sb.toString();
  }
  public Object clone() throws CloneNotSupportedException {
    return super.clone();
  }
}
