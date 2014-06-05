package com.sleepycat.je.cleaner;
class LookAheadCache {
  LookAheadCache(  int lookAheadCacheSize){
    usedMem=MemoryBudget.TREEMAP_OVERHEAD;
  }
  protected void hook166(  LNInfo info){
    usedMem+=info.getMemorySize();
    usedMem+=MemoryBudget.TREEMAP_ENTRY_OVERHEAD - 1;
    original(info);
  }
  protected void hook167(  LNInfo info){
    usedMem--;
    usedMem-=info.getMemorySize();
    usedMem-=MemoryBudget.TREEMAP_ENTRY_OVERHEAD + 1;
    original(info);
  }
}
