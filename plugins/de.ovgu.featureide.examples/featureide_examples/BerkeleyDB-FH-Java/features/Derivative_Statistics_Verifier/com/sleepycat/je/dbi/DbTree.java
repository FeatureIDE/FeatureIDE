package com.sleepycat.je.dbi;
public class DbTree {
  public boolean verify(  VerifyConfig config,  PrintStream out) throws DatabaseException {
    boolean ret=true;
    try {
      boolean ok=idDatabase.verify(config,idDatabase.getEmptyStats());
      if (!ok) {
        ret=false;
      }
      ok=nameDatabase.verify(config,nameDatabase.getEmptyStats());
      if (!ok) {
        ret=false;
      }
    }
 catch (    DatabaseException DE) {
      ret=false;
    }
    ret=this.hook292(config,out,ret);
    return ret;
  }
  protected void hook291(  CursorImpl cursor) throws DatabaseException {
  }
  protected boolean hook292(  VerifyConfig config,  PrintStream out,  boolean ret) throws DatabaseException {
    Locker locker=null;
    CursorImpl cursor=null;
    LockType lockType=LockType.NONE;
    try {
      locker=new BasicLocker(envImpl);
      cursor=new CursorImpl(idDatabase,locker);
      if (cursor.positionFirstOrLast(true,null)) {
        MapLN mapLN=(MapLN)cursor.getCurrentLNAlreadyLatched(lockType);
        DatabaseEntry keyDbt=new DatabaseEntry();
        DatabaseEntry dataDbt=new DatabaseEntry();
        while (true) {
          if (mapLN != null && !mapLN.isDeleted()) {
            DatabaseImpl dbImpl=mapLN.getDatabase();
            boolean ok=dbImpl.verify(config,dbImpl.getEmptyStats());
            if (!ok) {
              ret=false;
            }
          }
          OperationStatus status=cursor.getNext(keyDbt,dataDbt,lockType,true,false);
          if (status != OperationStatus.SUCCESS) {
            break;
          }
          mapLN=(MapLN)cursor.getCurrentLN(lockType);
        }
      }
    }
 catch (    DatabaseException e) {
      e.printStackTrace(out);
      ret=false;
    }
 finally {
      if (cursor != null) {
        this.hook291(cursor);
        cursor.close();
      }
      if (locker != null) {
        locker.operationEnd();
      }
    }
    return ret;
  }
}
