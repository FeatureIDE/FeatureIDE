package com.sleepycat.je.txn;
import de.ovgu.cide.jakutil.*;
/** 
 * LockGrantType is an enumeration of the possible results of a lock attempt.
 */
public class LockGrantType {
  private String name;
  public static final LockGrantType NEW=new LockGrantType("NEW");
  public static final LockGrantType WAIT_NEW=new LockGrantType("WAIT_NEW");
  public static final LockGrantType PROMOTION=new LockGrantType("PROMOTION");
  public static final LockGrantType WAIT_PROMOTION=new LockGrantType("WAIT_PROMOTION");
  public static final LockGrantType EXISTING=new LockGrantType("EXISTING");
  public static final LockGrantType DENIED=new LockGrantType("DENIED");
  public static final LockGrantType WAIT_RESTART=new LockGrantType("WAIT_RESTART");
  public static final LockGrantType NONE_NEEDED=new LockGrantType("NONE_NEEDED");
  private LockGrantType(  String name){
    this.name=name;
  }
  public String toString(){
    return name;
  }
}
