package com.sleepycat.je.tree;
import com.sleepycat.je.latch.LatchSupport;
import com.sleepycat.je.latch.SharedLatch;
public final class Tree {
  private SharedLatch rootLatch;
  private void releaseNodeLadderLatches(  ArrayList nodeLadder) throws DatabaseException {
    ListIterator iter=nodeLadder.listIterator(nodeLadder.size());
    while (iter.hasPrevious()) {
      SplitInfo info3=(SplitInfo)iter.previous();
      info3.child.releaseLatch();
    }
  }
  /** 
 * constructor helper
 */
  private void init(  DatabaseImpl database){
    rootLatch=LatchSupport.makeSharedLatch("RootLatch",(database != null) ? database.getDbEnvironment() : null);
    original(database);
  }
  /** 
 * Set the root for the tree. Should only be called within the root latch.
 */
  public void setRoot(  ChildReference newRoot,  boolean notLatched){
    assert (notLatched || rootLatch.isWriteLockedByCurrentThread());
    original(newRoot,notLatched);
  }
  protected void hook670(  WithRootLatched wrl) throws DatabaseException {
    try {
      original(wrl);
    }
  finally {
      rootLatch.release();
    }
  }
  protected void hook671(  WithRootLatched wrl) throws DatabaseException {
    try {
      original(wrl);
    }
  finally {
      rootLatch.release();
    }
  }
  protected void hook672(  byte[] idKey,  UtilizationTracker tracker,  IN subtreeRootIN,  ArrayList nodeLadder,  IN rootIN,  boolean rootNeedsUpdating) throws DatabaseException, NodeNotEmptyException, CursorsExistException {
    rootLatch.acquireExclusive();
    try {
      original(idKey,tracker,subtreeRootIN,nodeLadder,rootIN,rootNeedsUpdating);
    }
  finally {
      releaseNodeLadderLatches(nodeLadder);
      if (rootIN != null) {
        rootIN.releaseLatch();
      }
      rootLatch.release();
    }
  }
  /** 
 * This entire tree is empty, clear the root and log a new MapLN
 * @return the rootIN that has been detached, or null if there hasn't been
 * any removal.
 */
  private IN logTreeRemoval(  IN rootIN,  UtilizationTracker tracker) throws DatabaseException {
    assert rootLatch.isWriteLockedByCurrentThread();
    return original(rootIN,tracker);
  }
  protected void hook673() throws DatabaseException {
    assert rootLatch.isWriteLockedByCurrentThread();
    original();
  }
  protected IN hook674(  byte[] idKey,  byte[] mainKey,  IN in,  IN deletedSubtreeRoot) throws DatabaseException, NodeNotEmptyException, CursorsExistException {
    try {
      deletedSubtreeRoot=original(idKey,mainKey,in,deletedSubtreeRoot);
    }
  finally {
      in.releaseLatch();
    }
    return deletedSubtreeRoot;
  }
  protected void hook675(  DIN duplicateRoot) throws DatabaseException, NodeNotEmptyException, CursorsExistException {
    if (duplicateRoot != null) {
      duplicateRoot.releaseLatch();
    }
    original(duplicateRoot);
  }
  protected void hook676(  ArrayList nodeLadder) throws DatabaseException, NodeNotEmptyException, CursorsExistException {
    releaseNodeLadderLatches(nodeLadder);
    original(nodeLadder);
  }
  protected void hook677(  DIN dupRoot) throws DatabaseException {
    assert dupRoot.isLatchOwner();
    original(dupRoot);
  }
  protected void hook678(  DIN dupRoot) throws DatabaseException {
    assert dupRoot.isLatchOwner();
    original(dupRoot);
  }
  protected void hook679(  IN child) throws DatabaseException {
    child.releaseLatch();
    original(child);
  }
  protected void hook680(  IN child) throws DatabaseException {
    assert child.isLatchOwner();
    original(child);
  }
  protected void hook681(  IN potentialParent) throws DatabaseException {
    potentialParent.releaseLatchIfOwner();
    original(potentialParent);
  }
  protected void hook682(  IN searchResult) throws DatabaseException {
    searchResult.releaseLatchIfOwner();
    original(searchResult);
  }
  protected void hook683(  TreeLocation location,  byte[] mainKey,  byte[] dupKey,  LN ln,  boolean splitsAllowed,  boolean findDeletedEntries,  boolean searchDupTree,  boolean updateGeneration,  boolean exactSearch,  boolean indicateIfExact,  Node childNode) throws DatabaseException {
    try {
      original(location,mainKey,dupKey,ln,splitsAllowed,findDeletedEntries,searchDupTree,updateGeneration,exactSearch,indicateIfExact,childNode);
    }
 catch (    DatabaseException e) {
      location.bin.releaseLatchIfOwner();
      throw e;
    }
  }
  protected void hook684(  BIN oldBIN) throws DatabaseException {
    if (oldBIN != null) {
      oldBIN.releaseLatch();
    }
    original(oldBIN);
  }
  protected void hook685(  TreeLocation location,  byte[] dupKey,  DIN dupRoot,  LN ln,  boolean findDeletedEntries,  boolean indicateIfExact,  boolean exactSearch,  boolean splitsAllowed,  boolean updateGeneration) throws DatabaseException {
    dupRoot.latch();
    try {
      original(location,dupKey,dupRoot,ln,findDeletedEntries,indicateIfExact,exactSearch,splitsAllowed,updateGeneration);
    }
 catch (    DatabaseException e) {
      dupRoot.releaseLatchIfOwner();
      throw e;
    }
  }
  protected void hook686(  boolean traverseWithinDupTree,  boolean forward,  byte[] idKey,  IN next,  IN parent,  IN nextIN) throws DatabaseException {
    try {
      original(traverseWithinDupTree,forward,idKey,next,parent,nextIN);
    }
 catch (    DatabaseException e) {
      next.releaseLatchIfOwner();
      if (parent != null) {
        parent.releaseLatchIfOwner();
      }
      if (nextIN != null) {
        nextIN.releaseLatchIfOwner();
      }
      throw e;
    }
  }
  protected void hook687() throws DatabaseException {
    assert LatchSupport.countLatchesHeld() == 1 : LatchSupport.latchesHeldToString();
    original();
  }
  protected void hook688(  LogManager logManager,  INList inMemoryINs,  IN curRoot,  long curRootLsn,  long logLsn,  IN newRoot) throws DatabaseException {
    try {
      original(logManager,inMemoryINs,curRoot,curRootLsn,logLsn,newRoot);
    }
  finally {
      curRoot.releaseLatch();
    }
  }
  protected void hook689(  IN curRoot) throws DatabaseException {
    curRoot.latch();
    original(curRoot);
  }
  protected void hook690(  IN parent) throws DatabaseException {
    assert parent.isLatchOwner();
    original(parent);
  }
  protected void hook691(  IN parent) throws DatabaseException {
    parent.releaseLatch();
    original(parent);
  }
  protected void hook692(  IN parent) throws DatabaseException, Throwable {
    parent.releaseLatch();
    original(parent);
  }
  protected void hook693(  IN child) throws DatabaseException, Throwable {
    child.releaseLatch();
    original(child);
  }
  protected void hook694(  IN parent,  IN child) throws DatabaseException {
    if (child != null) {
      child.releaseLatchIfOwner();
    }
    parent.releaseLatchIfOwner();
    original(parent,child);
  }
  protected void hook695(  IN parent) throws DatabaseException, NodeNotEmptyException, CursorsExistException {
    assert parent.isLatchOwner();
    original(parent);
  }
  protected void hook696(  SplitInfo info5) throws DatabaseException, NodeNotEmptyException, CursorsExistException {
    info5.child.releaseLatch();
    original(info5);
  }
  protected void hook697(  ArrayList nodeLadder) throws DatabaseException, NodeNotEmptyException, CursorsExistException {
    releaseNodeLadderLatches(nodeLadder);
    original(nodeLadder);
  }
  protected void hook698(  IN parent,  byte[] key,  long nid,  boolean updateGeneration,  int index,  IN child) throws DatabaseException, SplitRequiredException {
    try {
      original(parent,key,nid,updateGeneration,index,child);
    }
 catch (    DatabaseException e) {
      if (child != null) {
        child.releaseLatchIfOwner();
      }
      parent.releaseLatchIfOwner();
      throw e;
    }
  }
  protected void hook699(  IN parent) throws DatabaseException, SplitRequiredException {
    assert parent.isLatchOwner();
    original(parent);
  }
  protected void hook700(  IN parent) throws DatabaseException, SplitRequiredException {
    parent.releaseLatch();
    original(parent);
  }
  protected void hook701(  boolean updateGeneration,  IN rootIN) throws DatabaseException {
    try {
      original(updateGeneration,rootIN);
    }
  finally {
      rootLatch.release();
    }
  }
  protected void hook702() throws DatabaseException {
    rootLatch.acquireShared();
    original();
  }
  protected void hook703(  LN ln,  byte[] key,  boolean allowDuplicates,  CursorImpl cursor,  LockResult lnLock,  EnvironmentImpl env,  LogManager logManager,  INList inMemoryINs,  BIN bin) throws DatabaseException {
    try {
      original(ln,key,allowDuplicates,cursor,lnLock,env,logManager,inMemoryINs,bin);
    }
  finally {
      cursor.releaseBIN();
    }
  }
  protected void hook704(  byte[] key,  BIN bin,  LN newLN,  CursorImpl cursor,  LockResult lnLock,  boolean allowDuplicates,  EnvironmentImpl env,  int index,  boolean successfulInsert,  DIN dupRoot,  Node n,  long binNid,  DBIN dupBin) throws DatabaseException {
    try {
      original(key,bin,newLN,cursor,lnLock,allowDuplicates,env,index,successfulInsert,dupRoot,n,binNid,dupBin);
    }
  finally {
      if (dupBin != null) {
        dupBin.releaseLatchIfOwner();
      }
      if (dupRoot != null) {
        dupRoot.releaseLatchIfOwner();
      }
    }
  }
  protected void hook705(  DIN dupRoot) throws DatabaseException {
    dupRoot.releaseLatch();
    original(dupRoot);
  }
  protected void hook706(  BIN bin,  int index,  DIN curRoot,  LogManager logManager,  INList inMemoryINs,  byte[] rootIdKey,  DIN newRoot,  long curRootLsn,  long logLsn) throws DatabaseException {
    try {
      original(bin,index,curRoot,logManager,inMemoryINs,rootIdKey,newRoot,curRootLsn,logLsn);
    }
  finally {
      curRoot.releaseLatch();
    }
  }
  protected void hook707(  DIN newRoot) throws DatabaseException {
    newRoot.latch();
    original(newRoot);
  }
  protected void hook708(  byte[] key,  LogManager logManager,  INList inMemoryINs,  LN newLN,  CursorImpl cursor,  EnvironmentImpl env,  DIN dupRoot,  DBIN dupBin,  BIN bin,  int index,  LN existingLN,  byte[] newLNKey,  Locker locker,  DupCountLN dupCountLN,  long firstDupCountLNLsn) throws DatabaseException {
    try {
      original(key,logManager,inMemoryINs,newLN,cursor,env,dupRoot,dupBin,bin,index,existingLN,newLNKey,locker,dupCountLN,firstDupCountLNLsn);
    }
 catch (    DatabaseException e) {
      dupBin.releaseLatchIfOwner();
      dupRoot.releaseLatchIfOwner();
      throw e;
    }
  }
  protected void hook709(  DBIN dupBin) throws DatabaseException {
    dupBin.latch();
    original(dupBin);
  }
  protected void hook710(  DIN dupRoot) throws DatabaseException {
    dupRoot.latch();
    original(dupRoot);
  }
  protected BIN hook711(  byte[] key,  LogManager logManager,  INList inMemoryINs,  BIN bin,  boolean rootLatchIsHeld) throws DatabaseException {
    try {
      bin=original(key,logManager,inMemoryINs,bin,rootLatchIsHeld);
    }
  finally {
      if (rootLatchIsHeld) {
        rootLatch.release();
      }
    }
    return bin;
  }
  protected void hook712(  BIN bin) throws DatabaseException {
    bin.releaseLatch();
    original(bin);
  }
  protected void hook713(  INList inList,  IN subtreeRoot,  UtilizationTracker tracker) throws DatabaseException {
    inList.latchMajor();
    try {
      original(inList,subtreeRoot,tracker);
    }
  finally {
      inList.releaseMajorLatch();
    }
  }
  protected void hook714(  INList inMemoryList) throws DatabaseException {
    rootLatch.acquireShared();
    try {
      original(inMemoryList);
    }
  finally {
      rootLatch.release();
    }
  }
  protected void hook715(  int index) throws DatabaseException {
    rootLatch.acquireShared();
    try {
      original(index);
    }
  finally {
      rootLatch.release();
    }
  }
  protected void hook728() throws DatabaseException {
    rootLatch.acquireExclusive();
    original();
  }
  protected void hook729() throws DatabaseException {
    rootLatch.acquireShared();
    original();
  }
  protected void hook730(  IN in) throws DatabaseException, NodeNotEmptyException, CursorsExistException {
    assert in.isLatchOwner();
    original(in);
  }
  protected void hook731(  TreeLocation location) throws DatabaseException {
    location.bin.releaseLatch();
    original(location);
  }
  protected void hook732() throws DatabaseException {
    assert (LatchSupport.countLatchesHeld() == 1) : LatchSupport.latchesHeldToString();
    original();
  }
  protected void hook733() throws DatabaseException {
    assert (LatchSupport.countLatchesHeld() == 0) : LatchSupport.latchesHeldToString();
    original();
  }
  protected void hook734(  IN next) throws DatabaseException {
    next.releaseLatch();
    original(next);
  }
  protected void hook735(  IN nextIN) throws DatabaseException {
    nextIN.latch();
    assert (LatchSupport.countLatchesHeld() == 2) : LatchSupport.latchesHeldToString();
    original(nextIN);
  }
  protected void hook736(  IN parent) throws DatabaseException {
    parent.releaseLatch();
    original(parent);
  }
  protected void hook737(  IN parent) throws DatabaseException {
    parent.releaseLatch();
    assert LatchSupport.countLatchesHeld() == 1 : LatchSupport.latchesHeldToString();
    original(parent);
  }
  protected void hook738(  IN parent) throws DatabaseException, SplitRequiredException {
    parent.releaseLatch();
    original(parent);
  }
  protected void hook739(  IN parent,  IN child) throws DatabaseException, SplitRequiredException {
    child.releaseLatch();
    parent.releaseLatch();
    original(parent,child);
  }
  protected void hook740(  IN child) throws DatabaseException, SplitRequiredException {
    child.releaseLatch();
    original(child);
  }
  protected void hook741(  BIN bin) throws DatabaseException {
    assert bin.isLatchOwner();
    original(bin);
  }
  protected void hook742(  DBIN dupBin) throws DatabaseException {
    dupBin.releaseLatch();
    original(dupBin);
  }
  protected void hook743(  CursorImpl cursor) throws DatabaseException {
    cursor.releaseBIN();
    original(cursor);
  }
  protected void hook744(  DIN dupRoot) throws DatabaseException {
    dupRoot.latch();
    original(dupRoot);
  }
  protected void hook745(  CursorImpl cursor) throws DatabaseException {
    cursor.releaseBIN();
    original(cursor);
  }
  protected void hook746(  CursorImpl cursor) throws DatabaseException {
    cursor.latchBIN();
    original(cursor);
  }
  protected void hook747(  DBIN dupBin) throws DatabaseException {
    dupBin.releaseLatch();
    original(dupBin);
  }
  protected void hook748() throws DatabaseException {
    rootLatch.acquireShared();
    original();
  }
  protected void hook749() throws DatabaseException {
    rootLatch.release();
    original();
  }
  protected void hook750(  BIN bin) throws DatabaseException {
    bin.latch();
    original(bin);
  }
  protected void hook751() throws DatabaseException {
    rootLatch.release();
    rootLatch.acquireExclusive();
    original();
  }
  protected void hook752() throws DatabaseException {
    rootLatch.release();
    original();
  }
  protected void hook753() throws DatabaseException {
    rootLatch.release();
    original();
  }
@MethodObject static class Tree_forceSplit {
    protected void hook722() throws DatabaseException, SplitRequiredException {
      isRootLatched=false;
      original();
    }
    protected void hook723() throws DatabaseException, SplitRequiredException {
      if (origParent.isDbRoot()) {
        _this.rootLatch.acquireExclusive();
        isRootLatched=true;
      }
      origParent.latch();
      original();
    }
    protected void hook724() throws DatabaseException, SplitRequiredException {
      child.latch();
      original();
    }
    protected void hook725() throws DatabaseException, SplitRequiredException {
      child.releaseLatch();
      original();
    }
    protected void hook726() throws DatabaseException, SplitRequiredException {
      assert isRootLatched;
      original();
    }
    protected void hook727() throws DatabaseException, SplitRequiredException {
      if (!success) {
        if (child != null) {
          child.releaseLatchIfOwner();
        }
        origParent.releaseLatchIfOwner();
      }
      if (nodeLadder.size() > 0) {
        iter=nodeLadder.listIterator(nodeLadder.size());
        while (iter.hasPrevious()) {
          info2=(SplitInfo)iter.previous();
          info2.child.releaseLatchIfOwner();
        }
      }
      if (isRootLatched) {
        _this.rootLatch.release();
      }
      original();
    }
  }
@MethodObject static class Tree_searchSplitsAllowed {
    protected void hook716() throws DatabaseException {
      try {
        original();
      }
  finally {
        if (rootLatched) {
          _this.rootLatch.release();
        }
      }
    }
    protected void hook717() throws DatabaseException {
      _this.rootLatch.acquireShared();
      rootLatched=true;
      rootLatchedExclusive=false;
      original();
    }
    protected void hook718() throws DatabaseException {
      rootIN.latch();
      original();
    }
    protected void hook719() throws DatabaseException {
      rootLatched=true;
      _this.rootLatch.acquireExclusive();
      original();
    }
    protected void hook720() throws DatabaseException {
      _this.splitRoot();
      _this.rootLatch.release();
      rootLatched=false;
      original();
    }
    protected void hook721() throws DatabaseException {
      b=!rootLatchedExclusive;
      if (b) {
        rootIN=null;
        _this.rootLatch.release();
        _this.rootLatch.acquireExclusive();
        rootLatchedExclusive=true;
      }
      original();
    }
  }
private class RootChildReference {
    protected void hook666() throws DatabaseException {
      if (getTarget() == null && !rootLatch.isWriteLockedByCurrentThread()) {
        rootLatch.release();
        rootLatch.acquireExclusive();
      }
      original();
    }
    protected void hook667(){
      assert rootLatch.isWriteLockedByCurrentThread();
      original();
    }
    protected void hook668(){
      assert rootLatch.isWriteLockedByCurrentThread();
      original();
    }
    protected void hook669(){
      assert rootLatch.isWriteLockedByCurrentThread();
      original();
    }
  }
}
