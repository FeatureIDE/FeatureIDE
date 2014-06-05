package com.sleepycat.je.cleaner;
public class UtilizationProfile {
  protected boolean hook186(  DatabaseImpl db,  boolean b) throws DatabaseException {
    b|=db.isDeleted();
    return original(db,b);
  }
}
