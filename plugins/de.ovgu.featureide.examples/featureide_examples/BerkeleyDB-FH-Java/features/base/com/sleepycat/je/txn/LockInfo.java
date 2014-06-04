package com.sleepycat.je.txn;
import java.util.Collections;
import java.util.Map;
import java.util.WeakHashMap;
import com.sleepycat.je.utilint.Tracer;
import de.ovgu.cide.jakutil.*;
/** 
 * LockInfo is a class that embodies information about a lock instance.  The
 * holding thread and the locktype are all contained in the object.
 */
public class LockInfo implements Cloneable {
  private Locker locker;
  private LockType lockType;
  private static boolean deadlockStackTrace=false;
  private static Map traceExceptionMap=Collections.synchronizedMap(new WeakHashMap());
private static class StackTraceAtLockTime extends Exception {
  }
  /** 
 * Called when the je.txn.deadlockStackTrace property is changed.
 */
  static void setDeadlockStackTrace(  boolean enable){
    deadlockStackTrace=enable;
  }
  /** 
 * For unit testing only.
 */
  public static boolean getDeadlockStackTrace(){
    return deadlockStackTrace;
  }
  /** 
 * Construct a new LockInfo.  public for Sizeof program.
 */
  public LockInfo(  Locker locker,  LockType lockType){
    this.locker=locker;
    this.lockType=lockType;
    if (deadlockStackTrace) {
      traceExceptionMap.put(this,new StackTraceAtLockTime());
    }
  }
  /** 
 * Change this lockInfo over to the prescribed locker.
 */
  void setLocker(  Locker locker){
    this.locker=locker;
  }
  /** 
 * @return The transaction associated with this Lock.
 */
  Locker getLocker(){
    return locker;
  }
  /** 
 * @return The LockType associated with this Lock.
 */
  void setLockType(  LockType lockType){
    this.lockType=lockType;
  }
  /** 
 * @return The LockType associated with this Lock.
 */
  LockType getLockType(){
    return lockType;
  }
  public Object clone() throws CloneNotSupportedException {
    return super.clone();
  }
  /** 
 * Debugging
 */
  public void dump(){
    System.out.println(this);
  }
  public String toString(){
    StringBuffer buf=new StringBuffer(500);
    buf.append("<LockInfo locker=\"");
    buf.append(locker);
    buf.append("\" type=\"");
    buf.append(lockType);
    buf.append("\"/>");
    if (deadlockStackTrace) {
      Exception traceException=(Exception)traceExceptionMap.get(this);
      if (traceException != null) {
        buf.append(" lock taken at: ");
        buf.append(Tracer.getStackTrace(traceException));
      }
    }
    return buf.toString();
  }
}
