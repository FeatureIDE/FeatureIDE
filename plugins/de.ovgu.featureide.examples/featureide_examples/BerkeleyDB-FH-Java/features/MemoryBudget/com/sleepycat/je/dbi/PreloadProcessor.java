package com.sleepycat.je.dbi;
class PreloadProcessor {
  protected void hook355(){
    if (envImpl.getMemoryBudget().getCacheMemoryUsage() > maxBytes) {
      throw DatabaseImpl.memoryExceededPreloadException;
    }
    original();
  }
}
