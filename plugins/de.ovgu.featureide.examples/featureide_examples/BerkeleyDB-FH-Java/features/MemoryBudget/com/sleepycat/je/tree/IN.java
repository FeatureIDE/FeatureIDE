package com.sleepycat.je.tree;
public class IN {
  private boolean inListResident;
  private int accumulatedDelta=0;
  /** 
 * Initialize the per-node memory count by computing its memory usage.
 */
  protected void initMemorySize(){
    inMemorySize=computeMemorySize();
  }
  public boolean verifyMemorySize(){
    long calcMemorySize=computeMemorySize();
    if (calcMemorySize != inMemorySize) {
      String msg="-Warning: Out of sync. " + "Should be " + calcMemorySize + " / actual: "+ inMemorySize+ " node: "+ getNodeId();
      this.hook615(msg);
      System.out.println(msg);
      return false;
    }
 else {
      return true;
    }
  }
  /** 
 * Return the number of bytes used by this IN.  Latching is up to the
 * caller.
 */
  public long getInMemorySize(){
    return inMemorySize;
  }
  private long getEntryInMemorySize(  int idx){
    return getEntryInMemorySize(entryKeyVals[idx],entryTargets[idx]);
  }
  protected long getEntryInMemorySize(  byte[] key,  Node target){
    long ret=0;
    if (key != null) {
      ret+=MemoryBudget.byteArraySize(key.length);
    }
    if (target != null) {
      ret+=target.getMemorySizeIncludedByParent();
    }
    return ret;
  }
  /** 
 * Count up the memory usage attributable to this node alone. LNs children
 * are counted by their BIN/DIN parents, but INs are not counted by their
 * parents because they are resident on the IN list.
 */
  protected long computeMemorySize(){
    MemoryBudget mb=databaseImpl.getDbEnvironment().getMemoryBudget();
    long calcMemorySize=getMemoryOverhead(mb);
    calcMemorySize+=computeLsnOverhead();
    for (int i=0; i < nEntries; i++) {
      calcMemorySize+=getEntryInMemorySize(i);
    }
    if (provisionalObsolete != null) {
      calcMemorySize+=provisionalObsolete.size() * MemoryBudget.LONG_LIST_PER_ITEM_OVERHEAD;
    }
    return calcMemorySize;
  }
  public static long computeOverhead(  DbConfigManager configManager) throws DatabaseException {
    return MemoryBudget.IN_FIXED_OVERHEAD + IN.computeArraysOverhead(configManager);
  }
  private int computeLsnOverhead(){
    if (entryLsnLongArray == null) {
      return MemoryBudget.byteArraySize(entryLsnByteArray.length);
    }
 else {
      return MemoryBudget.BYTE_ARRAY_OVERHEAD + entryLsnLongArray.length * MemoryBudget.LONG_OVERHEAD;
    }
  }
  protected static long computeArraysOverhead(  DbConfigManager configManager) throws DatabaseException {
    int capacity=configManager.getInt(EnvironmentParams.NODE_MAX);
    return MemoryBudget.byteArraySize(capacity) + (capacity * (2 * MemoryBudget.ARRAY_ITEM_OVERHEAD));
  }
  protected long getMemoryOverhead(  MemoryBudget mb){
    return mb.getINOverhead();
  }
  protected void updateMemorySize(  ChildReference oldRef,  ChildReference newRef){
    long delta=0;
    if (newRef != null) {
      delta=getEntryInMemorySize(newRef.getKey(),newRef.getTarget());
    }
    if (oldRef != null) {
      delta-=getEntryInMemorySize(oldRef.getKey(),oldRef.getTarget());
    }
    changeMemorySize(delta);
  }
  protected void updateMemorySize(  long oldSize,  long newSize){
    long delta=newSize - oldSize;
    changeMemorySize(delta);
  }
  void updateMemorySize(  Node oldNode,  Node newNode){
    long delta=0;
    if (newNode != null) {
      delta=newNode.getMemorySizeIncludedByParent();
    }
    if (oldNode != null) {
      delta-=oldNode.getMemorySizeIncludedByParent();
    }
    changeMemorySize(delta);
  }
  private void changeMemorySize(  long delta){
    inMemorySize+=delta;
    if (inListResident) {
      MemoryBudget mb=databaseImpl.getDbEnvironment().getMemoryBudget();
      accumulatedDelta+=delta;
      if (accumulatedDelta > ACCUMULATED_LIMIT || accumulatedDelta < -ACCUMULATED_LIMIT) {
        mb.updateTreeMemoryUsage(accumulatedDelta);
        accumulatedDelta=0;
      }
    }
  }
  public int getAccumulatedDelta(){
    return accumulatedDelta;
  }
  public void setInListResident(  boolean resident){
    inListResident=resident;
  }
  protected void hook615(  String msg){
  }
  /** 
 * Create a new IN.
 */
  IN(  DatabaseImpl db,  byte[] identifierKey,  int capacity,  int level){
    initMemorySize();
  }
  /** 
 * Initialize IN object.
 */
  protected void init(  DatabaseImpl db,  byte[] identifierKey,  int initialCapacity,  int level){
    original(db,identifierKey,initialCapacity,level);
    inListResident=false;
  }
  protected void hook637() throws DatabaseException {
    initMemorySize();
    original();
  }
  /** 
 * Initialize a node read in during recovery.
 */
  public void postRecoveryInit(  DatabaseImpl db,  long sourceLsn){
    original(db,sourceLsn);
    initMemorySize();
  }
  protected void hook638(  Node node) throws DatabaseException, LogFileNotFoundException, Exception {
    updateMemorySize(null,node);
    original(node);
  }
  /** 
 * Update the idx'th entry of this node. This flavor is used when the
 * target LN is being modified, by an operation like a delete or update. We
 * don't have to check whether the LSN has been nulled or not, because we
 * know an LSN existed before. Also, the modification of the target is done
 * in the caller, so instead of passing in the old and new nodes, we pass
 * in the old and new node sizes.
 */
  public void updateEntry(  int idx,  long lsn,  long oldLNSize,  long newLNSize){
    updateMemorySize(oldLNSize,newLNSize);
    original(idx,lsn,oldLNSize,newLNSize);
  }
  /** 
 * Add self and children to this in-memory IN list. Called by recovery, can
 * run with no latching.
 */
  void rebuildINList(  INList inList) throws DatabaseException {
    initMemorySize();
    original(inList);
  }
@MethodObject static class IN_splitInternal {
    protected void hook650() throws DatabaseException {
      newSize=_this.computeMemorySize();
      _this.updateMemorySize(oldMemorySize,newSize);
      original();
    }
  }
@MethodObject static class IN_deleteEntry {
    protected void hook648() throws DatabaseException {
      _this.updateMemorySize(oldLSNArraySize,_this.computeLsnOverhead());
      original();
    }
    protected void hook649() throws DatabaseException {
      _this.updateMemorySize(_this.getEntryInMemorySize(index),0);
      oldLSNArraySize=_this.computeLsnOverhead();
      original();
    }
  }
@MethodObject static class IN_trackProvisionalObsolete {
    void execute(){
      original();
      if (memDelta != 0) {
        _this.changeMemorySize(memDelta);
      }
    }
    protected void hook651(){
      child.changeMemorySize(0 - childMemDelta);
      memDelta+=childMemDelta;
      original();
    }
    protected void hook652(){
      childMemDelta=child.provisionalObsolete.size() * MemoryBudget.LONG_LIST_PER_ITEM_OVERHEAD;
      original();
    }
    protected void hook653(){
      memDelta+=MemoryBudget.LONG_LIST_PER_ITEM_OVERHEAD;
      original();
    }
    protected void hook654(){
      memDelta+=MemoryBudget.LONG_LIST_PER_ITEM_OVERHEAD;
      original();
    }
  }
@MethodObject static class IN_insertEntry1 {
    protected void hook645() throws DatabaseException {
      _this.updateMemorySize(0,_this.getEntryInMemorySize(index));
      original();
    }
    protected void hook646() throws DatabaseException {
      _this.changeMemorySize(_this.computeLsnOverhead() - oldSize);
      original();
    }
    protected void hook647() throws DatabaseException {
      oldSize=_this.computeLsnOverhead();
      original();
    }
  }
@MethodObject static class IN_updateEntryCompareKey {
    void execute(){
      oldSize=_this.getEntryInMemorySize(idx);
      original();
    }
    protected void hook644(){
      newSize=_this.getEntryInMemorySize(idx);
      _this.updateMemorySize(oldSize,newSize);
      original();
    }
  }
@MethodObject static class IN_updateEntry {
    void execute(){
      oldSize=_this.getEntryInMemorySize(idx);
      original();
      newSize=_this.getEntryInMemorySize(idx);
      _this.updateMemorySize(oldSize,newSize);
    }
  }
@MethodObject static class IN_setLsn {
    void execute(){
      oldSize=_this.computeLsnOverhead();
      original();
    }
    protected void hook639(){
      _this.changeMemorySize(_this.computeLsnOverhead() - oldSize);
      original();
    }
  }
@MethodObject static class IN_updateEntry2 {
    void execute(){
      oldSize=_this.getEntryInMemorySize(idx);
      original();
    }
    protected void hook642(){
      newSize=_this.getEntryInMemorySize(idx);
      _this.updateMemorySize(oldSize,newSize);
      original();
    }
  }
@MethodObject static class IN_flushProvisionalObsolete {
    protected void hook655() throws DatabaseException {
      _this.changeMemorySize(0 - memDelta);
      original();
    }
    protected void hook656() throws DatabaseException {
      memDelta=_this.provisionalObsolete.size() * MemoryBudget.LONG_LIST_PER_ITEM_OVERHEAD;
      original();
    }
  }
@MethodObject static class IN_updateEntry3 {
    void execute(){
      oldSize=_this.getEntryInMemorySize(idx);
      original();
    }
    protected void hook643(){
      newSize=_this.getEntryInMemorySize(idx);
      _this.updateMemorySize(oldSize,newSize);
      original();
    }
  }
@MethodObject static class IN_setEntry {
    void execute(){
      oldSize=_this.getEntryInMemorySize(idx);
      original();
    }
    protected void hook640(){
      newSize=_this.getEntryInMemorySize(idx);
      _this.updateMemorySize(oldSize,newSize);
      original();
    }
    protected void hook641(){
      oldSize=0;
      original();
    }
  }
}
