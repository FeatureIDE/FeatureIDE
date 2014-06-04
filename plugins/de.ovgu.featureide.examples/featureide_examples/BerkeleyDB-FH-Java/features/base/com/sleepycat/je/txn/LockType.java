package com.sleepycat.je.txn;
import de.ovgu.cide.jakutil.*;
/** 
 * LockType is a type safe enumeration of all lock types.  Methods on LockType
 * objects can be used to determine whether a type conflicts with another
 * type or can be upgraded to another type.
 */
public class LockType {
  /** 
 * Lock types.  Indexes must be kept manually synchronized in the matrixes
 * below.
 */
  public static final LockType READ=new LockType(0,false,"READ");
  public static final LockType WRITE=new LockType(1,true,"WRITE");
  public static final LockType RANGE_READ=new LockType(2,false,"RANGE_READ");
  public static final LockType RANGE_WRITE=new LockType(3,true,"RANGE_WRITE");
  public static final LockType RANGE_INSERT=new LockType(4,false,"RANGE_INSERT");
  /** 
 * NONE is used for requesting a dirty read and does not appear in the
 * conflict or upgrade matrices.
 */
  public static final LockType NONE=new LockType(5,false,"NONE");
  /** 
 * RESTART is used for waiting for a restart and does not appear in the
 * conflict or upgrade matrices.
 */
  public static final LockType RESTART=new LockType(6,false,"RESTART");
  /** 
 * Whenever the conflict matrix is changed be sure to update this.  For
 * every type that can cause a RESTART result call setCausesRestart.  This
 * could have been determined programmatically but I chose to maintain it
 * manually to avoid extra code size.
 */
static {
    RANGE_READ.setCausesRestart();
    RANGE_WRITE.setCausesRestart();
  }
  /** 
 * Lock conflict matrix.
 * @see #getConflict
 */
  private static LockConflict[][] conflictMatrix={{LockConflict.ALLOW,LockConflict.BLOCK,LockConflict.ALLOW,LockConflict.BLOCK,LockConflict.ALLOW},{LockConflict.BLOCK,LockConflict.BLOCK,LockConflict.BLOCK,LockConflict.BLOCK,LockConflict.ALLOW},{LockConflict.ALLOW,LockConflict.BLOCK,LockConflict.ALLOW,LockConflict.BLOCK,LockConflict.BLOCK},{LockConflict.BLOCK,LockConflict.BLOCK,LockConflict.BLOCK,LockConflict.BLOCK,LockConflict.BLOCK},{LockConflict.ALLOW,LockConflict.ALLOW,LockConflict.RESTART,LockConflict.RESTART,LockConflict.ALLOW}};
  /** 
 * Lock upgrade matrix.
 * @see #getUpgrade
 */
  private static LockUpgrade[][] upgradeMatrix={{LockUpgrade.EXISTING,LockUpgrade.WRITE_PROMOTE,LockUpgrade.RANGE_READ_IMMED,LockUpgrade.RANGE_WRITE_PROMOTE,LockUpgrade.ILLEGAL},{LockUpgrade.EXISTING,LockUpgrade.EXISTING,LockUpgrade.RANGE_WRITE_IMMED,LockUpgrade.RANGE_WRITE_IMMED,LockUpgrade.ILLEGAL},{LockUpgrade.EXISTING,LockUpgrade.RANGE_WRITE_PROMOTE,LockUpgrade.EXISTING,LockUpgrade.RANGE_WRITE_PROMOTE,LockUpgrade.ILLEGAL},{LockUpgrade.EXISTING,LockUpgrade.EXISTING,LockUpgrade.EXISTING,LockUpgrade.EXISTING,LockUpgrade.ILLEGAL},{LockUpgrade.ILLEGAL,LockUpgrade.ILLEGAL,LockUpgrade.ILLEGAL,LockUpgrade.ILLEGAL,LockUpgrade.EXISTING}};
  private int index;
  private boolean write;
  private String name;
  private boolean causesRestart;
  /** 
 * No lock types can be defined outside this class.
 */
  private LockType(  int index,  boolean write,  String name){
    this.index=index;
    this.write=write;
    this.name=name;
  }
  /** 
 * Returns true if this is a WRITE or RANGE_WRITE lock.  For RANGE_INSERT,
 * false is returned because RANGE_INSERT is used to lock the key following
 * the insertion key, not the insertion key itself.
 */
  public final boolean isWriteLock(){
    return write;
  }
  /** 
 * Specifies that when this type is requested it can result in
 * LockGrantType.RESTART.
 */
  private void setCausesRestart(){
    causesRestart=true;
  }
  /** 
 * Returns whether when this type is requested it can result in
 * LockGrantType.RESTART.
 */
  final boolean getCausesRestart(){
    return causesRestart;
  }
  /** 
 * Returns the LockConfict that results when this lock type is held and the
 * given lock type is requested by another locker.
 */
  LockConflict getConflict(  LockType requestedType){
    return conflictMatrix[index][requestedType.index];
  }
  /** 
 * Returns the LockUpgrade that results when this lock type is held and the
 * given lock type is requested by the same locker.
 * <p>For the returned LockUpgrade object, getIllegal will never return
 * true because this method fires an assertion if getIllegal returns true.
 */
  LockUpgrade getUpgrade(  LockType requestedType){
    LockUpgrade upgrade=upgradeMatrix[index][requestedType.index];
    assert !upgrade.getIllegal() : toString() + " to " + requestedType;
    return upgrade;
  }
  public String toString(){
    return name;
  }
}
