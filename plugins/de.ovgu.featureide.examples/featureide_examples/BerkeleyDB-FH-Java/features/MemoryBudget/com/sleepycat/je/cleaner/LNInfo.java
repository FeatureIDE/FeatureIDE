package com.sleepycat.je.cleaner;
public final class LNInfo {
  int getMemorySize(){
    int size=MemoryBudget.LN_INFO_OVERHEAD;
    if (ln != null) {
      size+=ln.getMemorySizeIncludedByParent();
    }
    if (key != null) {
      size+=MemoryBudget.byteArraySize(key.length);
    }
    if (dupKey != null) {
      size+=MemoryBudget.byteArraySize(dupKey.length);
    }
    return size;
  }
}
