package com.sleepycat.je.dbi;
public class DatabaseImpl {
@MethodObject static class DatabaseImpl_preload {
    protected void hook290() throws DatabaseException {
      cacheBudget=_this.envImpl.getMemoryBudget().getCacheBudget();
      if (maxBytes == 0) {
        maxBytes=cacheBudget;
      }
 else       if (maxBytes > cacheBudget) {
        throw new IllegalArgumentException("maxBytes parameter to Database.preload() was specified as " + maxBytes + " bytes \nbut the cache is only "+ cacheBudget+ " bytes.");
      }
      original();
    }
  }
}
