package com.sleepycat.je.evictor;
public class Evictor {
@MethodObject static class Evictor_doCriticalEviction {
    void execute() throws DatabaseException {
      mb=_this.envImpl.getMemoryBudget();
      currentUsage=mb.getCacheMemoryUsage();
      maxMem=mb.getCacheBudget();
      over=currentUsage - maxMem;
      if (over > mb.getCriticalThreshold()) {
        if (_this.DEBUG) {
          System.out.println("***critical detected:" + over);
        }
        _this.doEvict(_this.SOURCE_CRITICAL,true);
      }
      original();
    }
  }
}
