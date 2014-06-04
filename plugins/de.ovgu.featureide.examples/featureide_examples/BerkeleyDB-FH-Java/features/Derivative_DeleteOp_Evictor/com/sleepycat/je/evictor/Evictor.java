package com.sleepycat.je.evictor;
public class Evictor {
  protected boolean hook386(  DatabaseImpl db,  boolean b2) throws DatabaseException {
    b2=db.isDeleted();
    return original(db,b2);
  }
  protected boolean hook387(  DatabaseImpl db,  boolean b) throws DatabaseException {
    b|=db.isDeleteFinished();
    return original(db,b);
  }
}
