package com.sleepycat.je.dbi;
public class MemoryBudget {
  private final static int LONG_OVERHEAD_32=16;
  private final static int LONG_OVERHEAD_64=24;
  private final static int BYTE_ARRAY_OVERHEAD_32=16;
  private final static int BYTE_ARRAY_OVERHEAD_64=24;
  private final static int OBJECT_OVERHEAD_32=8;
  private final static int OBJECT_OVERHEAD_64=16;
  private final static int ARRAY_ITEM_OVERHEAD_32=4;
  private final static int ARRAY_ITEM_OVERHEAD_64=8;
  private final static int HASHMAP_OVERHEAD_32=120;
  private final static int HASHMAP_OVERHEAD_64=216;
  private final static int HASHMAP_ENTRY_OVERHEAD_32=24;
  private final static int HASHMAP_ENTRY_OVERHEAD_64=48;
  private final static int HASHSET_OVERHEAD_32=136;
  private final static int HASHSET_OVERHEAD_64=240;
  private final static int HASHSET_ENTRY_OVERHEAD_32=24;
  private final static int HASHSET_ENTRY_OVERHEAD_64=48;
  private final static int TWOHASHMAPS_OVERHEAD_32=240;
  private final static int TWOHASHMAPS_OVERHEAD_64=432;
  private final static int TREEMAP_OVERHEAD_32=40;
  private final static int TREEMAP_OVERHEAD_64=64;
  private final static int TREEMAP_ENTRY_OVERHEAD_32=32;
  private final static int TREEMAP_ENTRY_OVERHEAD_64=53;
  private final static int LN_OVERHEAD_32=24;
  private final static int LN_OVERHEAD_64=32;
  private final static int DUPCOUNTLN_OVERHEAD_32=24;
  private final static int DUPCOUNTLN_OVERHEAD_64=40;
  private final static int BIN_FIXED_OVERHEAD_32_14=344;
  private final static int BIN_FIXED_OVERHEAD_32_15=360;
  private final static int BIN_FIXED_OVERHEAD_64_15=528;
  private final static int DIN_FIXED_OVERHEAD_32_14=352;
  private final static int DIN_FIXED_OVERHEAD_32_15=360;
  private final static int DIN_FIXED_OVERHEAD_64_15=536;
  private final static int DBIN_FIXED_OVERHEAD_32_14=352;
  private final static int DBIN_FIXED_OVERHEAD_32_15=368;
  private final static int DBIN_FIXED_OVERHEAD_64_15=544;
  private final static int IN_FIXED_OVERHEAD_32_14=312;
  private final static int IN_FIXED_OVERHEAD_32_15=320;
  private final static int IN_FIXED_OVERHEAD_64_15=472;
  private final static int KEY_OVERHEAD_32=16;
  private final static int KEY_OVERHEAD_64=24;
  private final static int LOCK_OVERHEAD_32=32;
  private final static int LOCK_OVERHEAD_64=56;
  private final static int LOCKINFO_OVERHEAD_32=16;
  private final static int LOCKINFO_OVERHEAD_64=32;
  private final static int TXN_OVERHEAD_32_14=167;
  private final static int TXN_OVERHEAD_32_15=175;
  private final static int TXN_OVERHEAD_64_15=293;
  private final static int CHECKPOINT_REFERENCE_SIZE_32_14=32 + HASHSET_ENTRY_OVERHEAD_32;
  private final static int CHECKPOINT_REFERENCE_SIZE_32_15=40 + HASHSET_ENTRY_OVERHEAD_32;
  private final static int CHECKPOINT_REFERENCE_SIZE_64_15=56 + HASHSET_ENTRY_OVERHEAD_64;
  private final static int UTILIZATION_PROFILE_ENTRY_32=88;
  private final static int UTILIZATION_PROFILE_ENTRY_64=136;
  private final static int TFS_LIST_INITIAL_OVERHEAD_32=464;
  private final static int TFS_LIST_INITIAL_OVERHEAD_64=504;
  private final static int TFS_LIST_SEGMENT_OVERHEAD_32=440;
  private final static int TFS_LIST_SEGMENT_OVERHEAD_64=464;
  private final static int LN_INFO_OVERHEAD_32=24;
  private final static int LN_INFO_OVERHEAD_64=48;
  private final static int LONG_LIST_PER_ITEM_OVERHEAD_32=20;
  private final static int LONG_LIST_PER_ITEM_OVERHEAD_64=32;
  public static int LONG_OVERHEAD;
  public static int BYTE_ARRAY_OVERHEAD;
  public static int OBJECT_OVERHEAD;
  public static int ARRAY_ITEM_OVERHEAD;
  public static int HASHMAP_OVERHEAD;
  public static int HASHMAP_ENTRY_OVERHEAD;
  public static int HASHSET_OVERHEAD;
  public static int HASHSET_ENTRY_OVERHEAD;
  public static int TWOHASHMAPS_OVERHEAD;
  public static int TREEMAP_OVERHEAD;
  public static int TREEMAP_ENTRY_OVERHEAD;
  public static int LN_OVERHEAD;
  public static int DUPCOUNTLN_OVERHEAD;
  public static int BIN_FIXED_OVERHEAD;
  public static int DIN_FIXED_OVERHEAD;
  public static int DBIN_FIXED_OVERHEAD;
  public static int IN_FIXED_OVERHEAD;
  public static int KEY_OVERHEAD;
  public static int LOCK_OVERHEAD;
  public static int LOCKINFO_OVERHEAD;
  public static int TXN_OVERHEAD;
  public static int CHECKPOINT_REFERENCE_SIZE;
  public static int UTILIZATION_PROFILE_ENTRY;
  public static int TFS_LIST_INITIAL_OVERHEAD;
  public static int TFS_LIST_SEGMENT_OVERHEAD;
  public static int LN_INFO_OVERHEAD;
  public static int LONG_LIST_PER_ITEM_OVERHEAD;
  private final static String JVM_ARCH_PROPERTY="sun.arch.data.model";
  private final static String FORCE_JVM_ARCH="je.forceJVMArch";
  private long treeMemoryUsage;
  private long miscMemoryUsage;
  private Object memoryUsageSynchronizer=new Object();
  private int nLockTables;
  private long[] lockMemoryUsage;
  private long trackerBudget;
  private long cacheBudget;
  private long inOverhead;
  private long binOverhead;
  private long dinOverhead;
  private long dbinOverhead;
  /** 
 * Initialize the starting environment memory state
 */
  void initCacheMemoryUsage() throws DatabaseException {
synchronized (memoryUsageSynchronizer) {
      treeMemoryUsage=calcTreeCacheUsage();
    }
  }
  /** 
 * Public for testing.
 */
  public long calcTreeCacheUsage() throws DatabaseException {
    long totalSize=0;
    INList inList=envImpl.getInMemoryINs();
    totalSize=this.hook347(totalSize,inList);
    return totalSize;
  }
  /** 
 * Update the environment wide tree memory count, wake up the evictor if
 * necessary.
 * @param incrementnote that increment may be negative.
 */
  public void updateTreeMemoryUsage(  long increment){
synchronized (memoryUsageSynchronizer) {
      treeMemoryUsage+=increment;
    }
  }
  /** 
 * Update the environment wide misc memory count, wake up the evictor if
 * necessary.
 * @param incrementnote that increment may be negative.
 */
  public void updateMiscMemoryUsage(  long increment){
synchronized (memoryUsageSynchronizer) {
      miscMemoryUsage+=increment;
    }
  }
  public void updateLockMemoryUsage(  long increment,  int lockTableIndex){
    lockMemoryUsage[lockTableIndex]+=increment;
  }
  public long accumulateNewUsage(  IN in,  long newSize){
    return in.getInMemorySize() + newSize;
  }
  public void refreshTreeMemoryUsage(  long newSize){
synchronized (memoryUsageSynchronizer) {
      treeMemoryUsage=newSize;
    }
  }
  public long getCacheMemoryUsage(){
    long accLockMemoryUsage=0;
    if (nLockTables == 1) {
      accLockMemoryUsage=lockMemoryUsage[0];
    }
 else {
      for (int i=0; i < nLockTables; i++) {
        accLockMemoryUsage+=lockMemoryUsage[i];
      }
    }
    return treeMemoryUsage + miscMemoryUsage + accLockMemoryUsage;
  }
  /** 
 * Used for unit testing.
 */
  public long getTreeMemoryUsage(){
    return treeMemoryUsage;
  }
  public long getTrackerBudget(){
    return trackerBudget;
  }
  public long getCacheBudget(){
    return cacheBudget;
  }
  public long getINOverhead(){
    return inOverhead;
  }
  public long getBINOverhead(){
    return binOverhead;
  }
  public long getDINOverhead(){
    return dinOverhead;
  }
  public long getDBINOverhead(){
    return dbinOverhead;
  }
  /** 
 * Returns the memory size occupied by a byte array of a given length.
 */
  public static int byteArraySize(  int arrayLen){
    int size=BYTE_ARRAY_OVERHEAD;
    if (arrayLen > 4) {
      size+=((arrayLen - 4 + 7) / 8) * 8;
    }
    return size;
  }
  protected long hook347(  long totalSize,  INList inList) throws DatabaseException {
    Iterator iter=inList.iterator();
    while (iter.hasNext()) {
      IN in=(IN)iter.next();
      long size=in.getInMemorySize();
      totalSize+=size;
    }
    return totalSize;
  }
  protected void hook351(  DbConfigManager configManager) throws DatabaseException {
    inOverhead=IN.computeOverhead(configManager);
    binOverhead=BIN.computeOverhead(configManager);
    dinOverhead=DIN.computeOverhead(configManager);
    dbinOverhead=DBIN.computeOverhead(configManager);
    original(configManager);
  }
@MethodObject static class MemoryBudget_sinit {
    void execute(){
      is64=false;
      isJVM14=true;
      original();
      overrideArch=System.getProperty(FORCE_JVM_ARCH);
      try {
        if (overrideArch == null) {
          arch=System.getProperty(JVM_ARCH_PROPERTY);
          if (arch != null) {
            is64=Integer.parseInt(arch) == 64;
          }
        }
 else {
          is64=Integer.parseInt(overrideArch) == 64;
        }
      }
 catch (      NumberFormatException NFE) {
        NFE.printStackTrace(System.err);
      }
      if (is64) {
        if (isJVM14) {
          RE=new RuntimeException("1.4 based 64 bit JVM not supported");
          RE.printStackTrace(System.err);
          throw RE;
        }
        LONG_OVERHEAD=LONG_OVERHEAD_64;
        BYTE_ARRAY_OVERHEAD=BYTE_ARRAY_OVERHEAD_64;
        OBJECT_OVERHEAD=OBJECT_OVERHEAD_64;
        ARRAY_ITEM_OVERHEAD=ARRAY_ITEM_OVERHEAD_64;
        HASHMAP_OVERHEAD=HASHMAP_OVERHEAD_64;
        HASHMAP_ENTRY_OVERHEAD=HASHMAP_ENTRY_OVERHEAD_64;
        HASHSET_OVERHEAD=HASHSET_OVERHEAD_64;
        HASHSET_ENTRY_OVERHEAD=HASHSET_ENTRY_OVERHEAD_64;
        TWOHASHMAPS_OVERHEAD=TWOHASHMAPS_OVERHEAD_64;
        TREEMAP_OVERHEAD=TREEMAP_OVERHEAD_64;
        TREEMAP_ENTRY_OVERHEAD=TREEMAP_ENTRY_OVERHEAD_64;
        LN_OVERHEAD=LN_OVERHEAD_64;
        DUPCOUNTLN_OVERHEAD=DUPCOUNTLN_OVERHEAD_64;
        BIN_FIXED_OVERHEAD=BIN_FIXED_OVERHEAD_64_15;
        DIN_FIXED_OVERHEAD=DIN_FIXED_OVERHEAD_64_15;
        DBIN_FIXED_OVERHEAD=DBIN_FIXED_OVERHEAD_64_15;
        IN_FIXED_OVERHEAD=IN_FIXED_OVERHEAD_64_15;
        TXN_OVERHEAD=TXN_OVERHEAD_64_15;
        CHECKPOINT_REFERENCE_SIZE=CHECKPOINT_REFERENCE_SIZE_64_15;
        KEY_OVERHEAD=KEY_OVERHEAD_64;
        LOCK_OVERHEAD=LOCK_OVERHEAD_64;
        LOCKINFO_OVERHEAD=LOCKINFO_OVERHEAD_64;
        UTILIZATION_PROFILE_ENTRY=UTILIZATION_PROFILE_ENTRY_64;
        TFS_LIST_INITIAL_OVERHEAD=TFS_LIST_INITIAL_OVERHEAD_64;
        TFS_LIST_SEGMENT_OVERHEAD=TFS_LIST_SEGMENT_OVERHEAD_64;
        LN_INFO_OVERHEAD=LN_INFO_OVERHEAD_64;
        LONG_LIST_PER_ITEM_OVERHEAD=LONG_LIST_PER_ITEM_OVERHEAD_64;
      }
 else {
        LONG_OVERHEAD=LONG_OVERHEAD_32;
        BYTE_ARRAY_OVERHEAD=BYTE_ARRAY_OVERHEAD_32;
        OBJECT_OVERHEAD=OBJECT_OVERHEAD_32;
        ARRAY_ITEM_OVERHEAD=ARRAY_ITEM_OVERHEAD_32;
        HASHMAP_OVERHEAD=HASHMAP_OVERHEAD_32;
        HASHMAP_ENTRY_OVERHEAD=HASHMAP_ENTRY_OVERHEAD_32;
        HASHSET_OVERHEAD=HASHSET_OVERHEAD_32;
        HASHSET_ENTRY_OVERHEAD=HASHSET_ENTRY_OVERHEAD_32;
        TWOHASHMAPS_OVERHEAD=TWOHASHMAPS_OVERHEAD_32;
        TREEMAP_OVERHEAD=TREEMAP_OVERHEAD_32;
        TREEMAP_ENTRY_OVERHEAD=TREEMAP_ENTRY_OVERHEAD_32;
        LN_OVERHEAD=LN_OVERHEAD_32;
        DUPCOUNTLN_OVERHEAD=DUPCOUNTLN_OVERHEAD_32;
        if (isJVM14) {
          BIN_FIXED_OVERHEAD=BIN_FIXED_OVERHEAD_32_14;
          DIN_FIXED_OVERHEAD=DIN_FIXED_OVERHEAD_32_14;
          DBIN_FIXED_OVERHEAD=DBIN_FIXED_OVERHEAD_32_14;
          IN_FIXED_OVERHEAD=IN_FIXED_OVERHEAD_32_14;
          TXN_OVERHEAD=TXN_OVERHEAD_32_14;
          CHECKPOINT_REFERENCE_SIZE=CHECKPOINT_REFERENCE_SIZE_32_14;
        }
 else {
          BIN_FIXED_OVERHEAD=BIN_FIXED_OVERHEAD_32_15;
          DIN_FIXED_OVERHEAD=DIN_FIXED_OVERHEAD_32_15;
          DBIN_FIXED_OVERHEAD=DBIN_FIXED_OVERHEAD_32_15;
          IN_FIXED_OVERHEAD=IN_FIXED_OVERHEAD_32_15;
          TXN_OVERHEAD=TXN_OVERHEAD_32_15;
          CHECKPOINT_REFERENCE_SIZE=CHECKPOINT_REFERENCE_SIZE_32_15;
        }
        KEY_OVERHEAD=KEY_OVERHEAD_32;
        LOCK_OVERHEAD=LOCK_OVERHEAD_32;
        LOCKINFO_OVERHEAD=LOCKINFO_OVERHEAD_32;
        UTILIZATION_PROFILE_ENTRY=UTILIZATION_PROFILE_ENTRY_32;
        TFS_LIST_INITIAL_OVERHEAD=TFS_LIST_INITIAL_OVERHEAD_32;
        TFS_LIST_SEGMENT_OVERHEAD=TFS_LIST_SEGMENT_OVERHEAD_32;
        LN_INFO_OVERHEAD=LN_INFO_OVERHEAD_32;
        LONG_LIST_PER_ITEM_OVERHEAD=LONG_LIST_PER_ITEM_OVERHEAD_32;
      }
    }
  }
@MethodObject static class MemoryBudget_reset {
    void execute() throws DatabaseException {
      original();
      _this.trackerBudget=true ? newTrackerBudget : newMaxMemory;
      _this.cacheBudget=newMaxMemory - newLogBufferBudget;
      _this.nLockTables=configManager.getInt(EnvironmentParams.N_LOCK_TABLES);
      _this.lockMemoryUsage=new long[_this.nLockTables];
    }
  }
}
