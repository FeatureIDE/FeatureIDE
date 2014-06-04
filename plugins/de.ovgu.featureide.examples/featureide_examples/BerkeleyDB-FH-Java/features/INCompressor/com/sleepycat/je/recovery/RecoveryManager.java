package com.sleepycat.je.recovery;
public class RecoveryManager {
  protected void hook594(  DatabaseImpl db,  TreeLocation location,  byte[] deletedKey) throws DatabaseException {
    if (deletedKey != null) {
      db.getDbEnvironment().addToCompressorQueue(location.bin,new Key(deletedKey),false);
    }
    original(db,location,deletedKey);
  }
  protected static void hook595(  DatabaseImpl db,  TreeLocation location,  byte[] deletedKey) throws DatabaseException {
    db.getDbEnvironment().addToCompressorQueue(location.bin,new Key(deletedKey),false);
    original(db,location,deletedKey);
  }
}
