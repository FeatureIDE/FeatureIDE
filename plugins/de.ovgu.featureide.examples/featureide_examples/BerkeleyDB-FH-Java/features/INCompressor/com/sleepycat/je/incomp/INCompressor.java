package com.sleepycat.je.incomp;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.logging.Level;
import com.sleepycat.je.DatabaseException;
import com.sleepycat.je.cleaner.TrackedFileSummary;
import com.sleepycat.je.cleaner.UtilizationTracker;
import com.sleepycat.je.config.EnvironmentParams;
import com.sleepycat.je.dbi.DatabaseImpl;
import com.sleepycat.je.dbi.DbTree;
import com.sleepycat.je.dbi.EnvironmentImpl;
import com.sleepycat.je.tree.BIN;
import com.sleepycat.je.tree.BINReference;
import com.sleepycat.je.tree.CursorsExistException;
import com.sleepycat.je.tree.DBIN;
import com.sleepycat.je.tree.DIN;
import com.sleepycat.je.tree.IN;
import com.sleepycat.je.tree.Key;
import com.sleepycat.je.tree.Node;
import com.sleepycat.je.tree.NodeNotEmptyException;
import com.sleepycat.je.tree.Tree;
import com.sleepycat.je.tree.Tree.SearchType;
import com.sleepycat.je.utilint.DaemonThread;
import com.sleepycat.je.utilint.PropUtil;
import com.sleepycat.je.utilint.Tracer;
import de.ovgu.cide.jakutil.*;
/** 
 * The IN Compressor.  JE compression consist of removing delete entries from
 * BINs, and pruning empty IN/BINs from the tree. Compression is carried out by
 * either a daemon thread or lazily by operations (namely checkpointing and
 * eviction) that are writing INS.
 */
public class INCompressor extends DaemonThread {
  private static final String TRACE_COMPRESS="INCompress:";
  private static final boolean DEBUG=false;
  private EnvironmentImpl env;
  private long lockTimeout;
  private Map binRefQueue;
  private Object binRefQueueSync;
  public INCompressor(  EnvironmentImpl env,  long waitTime,  String name) throws DatabaseException {
    super(waitTime,name,env);
    this.env=env;
    lockTimeout=PropUtil.microsToMillis(env.getConfigManager().getLong(EnvironmentParams.COMPRESSOR_LOCK_TIMEOUT));
    binRefQueue=new HashMap();
    binRefQueueSync=new Object();
  }
  public String toString(){
    StringBuffer sb=new StringBuffer();
    sb.append("<INCompressor name=\"").append(name).append("\"/>");
    return sb.toString();
  }
  synchronized public void clearEnv(){
    env=null;
  }
  /** 
 * The default daemon work queue is not used because we need a map, not a
 * set.
 */
  public void addToQueue(  Object o) throws DatabaseException {
    throw new DatabaseException("INCompressor.addToQueue should never be called.");
  }
  public int getBinRefQueueSize() throws DatabaseException {
    int size=0;
synchronized (binRefQueueSync) {
      size=binRefQueue.size();
    }
    return size;
  }
  /** 
 * Adds the BIN and deleted Key to the queue if the BIN is not already in
 * the queue, or adds the deleted key to an existing entry if one exists.
 */
  public void addBinKeyToQueue(  BIN bin,  Key deletedKey,  boolean doWakeup) throws DatabaseException {
synchronized (binRefQueueSync) {
      addBinKeyToQueueAlreadyLatched(bin,deletedKey);
    }
    if (doWakeup) {
      wakeup();
    }
  }
  /** 
 * Adds the BINReference to the queue if the BIN is not already in the
 * queue, or adds the deleted keys to an existing entry if one exists.
 */
  public void addBinRefToQueue(  BINReference binRef,  boolean doWakeup) throws DatabaseException {
synchronized (binRefQueueSync) {
      addBinRefToQueueAlreadyLatched(binRef);
    }
    if (doWakeup) {
      wakeup();
    }
  }
  /** 
 * Adds an entire collection of BINReferences to the queue at once.  Use
 * this to avoid latching for each add.
 */
  public void addMultipleBinRefsToQueue(  Collection binRefs,  boolean doWakeup) throws DatabaseException {
synchronized (binRefQueueSync) {
      Iterator it=binRefs.iterator();
      while (it.hasNext()) {
        BINReference binRef=(BINReference)it.next();
        addBinRefToQueueAlreadyLatched(binRef);
      }
    }
    if (doWakeup) {
      wakeup();
    }
  }
  /** 
 * Adds the BINReference with the latch held.
 */
  private void addBinRefToQueueAlreadyLatched(  BINReference binRef){
    Long node=new Long(binRef.getNodeId());
    BINReference existingRef=(BINReference)binRefQueue.get(node);
    if (existingRef != null) {
      existingRef.addDeletedKeys(binRef);
    }
 else {
      binRefQueue.put(node,binRef);
    }
  }
  /** 
 * Adds the BIN and deleted Key with the latch held.
 */
  private void addBinKeyToQueueAlreadyLatched(  BIN bin,  Key deletedKey){
    Long node=new Long(bin.getNodeId());
    BINReference existingRef=(BINReference)binRefQueue.get(node);
    if (existingRef != null) {
      if (deletedKey != null) {
        existingRef.addDeletedKey(deletedKey);
      }
    }
 else {
      BINReference binRef=bin.createReference();
      if (deletedKey != null) {
        binRef.addDeletedKey(deletedKey);
      }
      binRefQueue.put(node,binRef);
    }
  }
  public boolean exists(  long nodeId){
    Long node=new Long(nodeId);
synchronized (binRefQueueSync) {
      return (binRefQueue.get(node) != null);
    }
  }
  private BINReference removeCompressibleBinReference(  long nodeId){
    Long node=new Long(nodeId);
    BINReference foundRef=null;
synchronized (binRefQueueSync) {
      BINReference target=(BINReference)binRefQueue.remove(node);
      if (target != null) {
        if (target.deletedKeysExist()) {
          foundRef=target;
        }
 else {
          binRefQueue.put(node,target);
        }
      }
    }
    return foundRef;
  }
  /** 
 * Return the number of retries when a deadlock exception occurs.
 */
  protected int nDeadlockRetries() throws DatabaseException {
    return env.getConfigManager().getInt(EnvironmentParams.COMPRESSOR_RETRY);
  }
  public synchronized void onWakeup() throws DatabaseException {
    if (env.isClosed()) {
      return;
    }
    this.hook403();
    doCompress();
  }
  /** 
 * The real work to doing a compress. This may be called by the compressor
 * thread or programatically.
 */
  public synchronized void doCompress() throws DatabaseException {
    if (!isRunnable()) {
      return;
    }
    Map queueSnapshot=null;
    int binQueueSize=0;
synchronized (binRefQueueSync) {
      binQueueSize=binRefQueue.size();
      if (binQueueSize > 0) {
        queueSnapshot=binRefQueue;
        binRefQueue=new HashMap();
      }
    }
    if (binQueueSize > 0) {
      this.hook404();
      this.hook392(binQueueSize);
      this.hook393();
      UtilizationTracker tracker=new UtilizationTracker(env);
      Map dbCache=new HashMap();
      DbTree dbTree=env.getDbMapTree();
      BINSearch binSearch=new BINSearch();
      try {
        Iterator it=queueSnapshot.values().iterator();
        while (it.hasNext()) {
          if (env.isClosed()) {
            return;
          }
          BINReference binRef=(BINReference)it.next();
          if (!findDBAndBIN(binSearch,binRef,dbTree,dbCache)) {
            continue;
          }
          if (binRef.deletedKeysExist()) {
            boolean requeued=compressBin(binSearch.db,binSearch.bin,binRef,tracker);
            if (!requeued) {
              checkForRelocatedSlots(binSearch.db,binRef,tracker);
            }
          }
 else {
            BIN foundBin=binSearch.bin;
            byte[] idKey=foundBin.getIdentifierKey();
            boolean isDBIN=foundBin.containsDuplicates();
            byte[] dupKey=null;
            if (isDBIN) {
              dupKey=((DBIN)foundBin).getDupKey();
            }
            this.hook394(foundBin);
            pruneBIN(binSearch.db,binRef,idKey,isDBIN,dupKey,tracker);
          }
        }
        TrackedFileSummary[] summaries=tracker.getTrackedFiles();
        if (summaries.length > 0) {
          env.getUtilizationProfile().countAndLogSummaries(summaries);
        }
      }
  finally {
        this.hook395();
        this.hook405();
      }
    }
  }
  /** 
 * Compresses a single BIN and then deletes the BIN if it is empty.
 * @param bin is latched when this method is called, and unlatched when it
 * returns.
 * @return true if the BINReference was requeued by this method.
 */
  private boolean compressBin(  DatabaseImpl db,  BIN bin,  BINReference binRef,  UtilizationTracker tracker) throws DatabaseException {
    boolean empty=false;
    boolean requeued=false;
    byte[] idKey=bin.getIdentifierKey();
    byte[] dupKey=null;
    boolean isDBIN=bin.containsDuplicates();
    this.hook396(bin,binRef,empty,requeued,dupKey,isDBIN);
    if (empty) {
      requeued=pruneBIN(db,binRef,idKey,isDBIN,dupKey,tracker);
    }
    return requeued;
  }
  /** 
 * If the target BIN is empty, attempt to remove the empty branch of the 
 * tree.
 * @return true if the pruning was unable to proceed and the BINReference
 * was requeued.
 */
  private boolean pruneBIN(  DatabaseImpl dbImpl,  BINReference binRef,  byte[] idKey,  boolean containsDups,  byte[] dupKey,  UtilizationTracker tracker) throws DatabaseException {
    boolean requeued=false;
    try {
      Tree tree=dbImpl.getTree();
      if (containsDups) {
        tree.deleteDup(idKey,dupKey,tracker);
      }
 else {
        tree.delete(idKey,tracker);
      }
      this.hook406();
    }
 catch (    NodeNotEmptyException NNEE) {
      this.hook407();
    }
catch (    CursorsExistException e) {
      addBinRefToQueue(binRef,false);
      this.hook408();
      requeued=true;
    }
    return requeued;
  }
  private void checkForRelocatedSlots(  DatabaseImpl db,  BINReference binRef,  UtilizationTracker tracker) throws DatabaseException {
    Iterator iter=binRef.getDeletedKeyIterator();
    if (iter != null) {
      byte[] mainKey=binRef.getKey();
      boolean isDup=(binRef.getData() != null);
      while (iter.hasNext()) {
        Key key=(Key)iter.next();
        BIN splitBin=isDup ? searchForBIN(db,mainKey,key.getKey()) : searchForBIN(db,key.getKey(),null);
        if (splitBin != null) {
          BINReference splitBinRef=splitBin.createReference();
          splitBinRef.addDeletedKey(key);
          compressBin(db,splitBin,splitBinRef,tracker);
        }
      }
    }
  }
  private boolean isRunnable() throws DatabaseException {
    return true;
  }
  /** 
 * Search the tree for the BIN or DBIN that corresponds to this
 * BINReference.
 * @param binRef the BINReference that indicates the bin we want.
 * @return the BIN or DBIN that corresponds to this BINReference. The
 * node is latched upon return. Returns null if the BIN can't be found.
 */
  public BIN searchForBIN(  DatabaseImpl db,  BINReference binRef) throws DatabaseException {
    return searchForBIN(db,binRef.getKey(),binRef.getData());
  }
  private BIN searchForBIN(  DatabaseImpl db,  byte[] mainKey,  byte[] dupKey) throws DatabaseException {
    try {
      Tree tree=db.getTree();
      IN in=tree.search(mainKey,SearchType.NORMAL,-1,null,false);
      if (in == null) {
        return null;
      }
      if (dupKey == null) {
        return (BIN)in;
      }
      DIN duplicateRoot=null;
      DBIN duplicateBin=null;
      BIN bin=(BIN)in;
      this.hook397(mainKey,dupKey,tree,duplicateRoot,duplicateBin,bin);
      throw ReturnHack.returnObject;
    }
 catch (    ReturnObject r) {
      return (BIN)r.value;
    }
  }
  /** 
 * Lazily compress a single BIN. Do not do any pruning. The target IN
 * should be latched when we enter, and it will be remain latched.
 */
  public void lazyCompress(  IN in) throws DatabaseException {
    if (!in.isCompressible()) {
      return;
    }
    this.hook398(in);
    BIN bin=(BIN)in;
    int nCursors=bin.nCursors();
    if (nCursors > 0) {
      return;
    }
 else {
      BINReference binRef=removeCompressibleBinReference(bin.getNodeId());
      if ((binRef == null) || (!binRef.deletedKeysExist())) {
        return;
      }
 else {
        boolean requeued=bin.compress(binRef,false);
        this.hook409();
        if (!requeued && binRef.deletedKeysExist()) {
          addBinRefToQueue(binRef,false);
          this.hook410();
        }
 else {
          if (bin.getNEntries() == 0) {
            addBinRefToQueue(binRef,false);
            this.hook411();
          }
        }
      }
    }
  }
  private boolean findDBAndBIN(  BINSearch binSearch,  BINReference binRef,  DbTree dbTree,  Map dbCache) throws DatabaseException {
    binSearch.db=dbTree.getDb(binRef.getDatabaseId(),lockTimeout,dbCache);
    boolean close=binSearch.db == null;
    close=this.hook415(binSearch,close);
    if (close) {
      this.hook412();
      return false;
    }
    this.hook391();
    binSearch.bin=searchForBIN(binSearch.db,binRef);
    if ((binSearch.bin == null) || binSearch.bin.getNodeId() != binRef.getNodeId()) {
      this.hook399(binSearch);
      this.hook413();
      return false;
    }
    return true;
  }
private static class BINSearch {
    public DatabaseImpl db;
    public BIN bin;
  }
  protected void hook391() throws DatabaseException {
  }
  protected void hook392(  int binQueueSize) throws DatabaseException {
  }
  protected void hook393() throws DatabaseException {
  }
  protected void hook394(  BIN foundBin) throws DatabaseException {
  }
  protected void hook395() throws DatabaseException {
  }
  protected void hook396(  BIN bin,  BINReference binRef,  boolean empty,  boolean requeued,  byte[] dupKey,  boolean isDBIN) throws DatabaseException {
    int nCursors=bin.nCursors();
    if (nCursors > 0) {
      addBinRefToQueue(binRef,false);
      requeued=true;
      this.hook414();
    }
 else {
      requeued=bin.compress(binRef,true);
      if (!requeued) {
        empty=(bin.getNEntries() == 0);
        if (empty) {
          if (isDBIN) {
            dupKey=((DBIN)bin).getDupKey();
          }
        }
      }
    }
  }
  protected void hook397(  byte[] mainKey,  byte[] dupKey,  Tree tree,  DIN duplicateRoot,  DBIN duplicateBin,  BIN bin) throws DatabaseException {
    int index=bin.findEntry(mainKey,false,true);
    if (index >= 0) {
      Node node=null;
      if (!bin.isEntryKnownDeleted(index)) {
        node=bin.fetchTarget(index);
      }
      if (node == null) {
        this.hook400(bin);
        throw new ReturnObject(null);
      }
      if (node.containsDuplicates()) {
        duplicateRoot=(DIN)node;
        this.hook401(duplicateRoot,bin);
        duplicateBin=(DBIN)tree.searchSubTree(duplicateRoot,dupKey,SearchType.NORMAL,-1,null,false);
        throw new ReturnObject(duplicateBin);
      }
 else {
        throw new ReturnObject(bin);
      }
    }
 else {
      this.hook402(bin);
      throw new ReturnObject(null);
    }
  }
  protected void hook398(  IN in) throws DatabaseException {
  }
  protected void hook399(  BINSearch binSearch) throws DatabaseException {
  }
  protected void hook400(  BIN bin) throws DatabaseException {
  }
  protected void hook401(  DIN duplicateRoot,  BIN bin) throws DatabaseException {
  }
  protected void hook402(  BIN bin) throws DatabaseException {
  }
  protected void hook403() throws DatabaseException {
  }
  protected void hook404() throws DatabaseException {
  }
  protected void hook405() throws DatabaseException {
  }
  protected void hook406() throws DatabaseException, NodeNotEmptyException, CursorsExistException {
  }
  protected void hook407() throws DatabaseException {
  }
  protected void hook408() throws DatabaseException {
  }
  protected void hook409() throws DatabaseException {
  }
  protected void hook410() throws DatabaseException {
  }
  protected void hook411() throws DatabaseException {
  }
  protected void hook412() throws DatabaseException {
  }
  protected void hook413() throws DatabaseException {
  }
  protected void hook414() throws DatabaseException {
  }
  protected boolean hook415(  BINSearch binSearch,  boolean close) throws DatabaseException {
    return close;
  }
}
