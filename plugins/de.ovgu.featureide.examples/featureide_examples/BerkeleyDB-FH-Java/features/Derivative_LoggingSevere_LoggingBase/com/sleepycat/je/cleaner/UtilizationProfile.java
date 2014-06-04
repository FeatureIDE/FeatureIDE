package com.sleepycat.je.cleaner;
public class UtilizationProfile {
  protected void hook177(  long fileNum,  int sequence,  OperationStatus status) throws DatabaseException {
    if (status == OperationStatus.KEYEXIST) {
      env.getLogger().log(Level.SEVERE,"Cleaner duplicate key sequence file=0x" + Long.toHexString(fileNum) + " sequence=0x"+ Long.toHexString(sequence));
    }
    original(fileNum,sequence,status);
  }
}
