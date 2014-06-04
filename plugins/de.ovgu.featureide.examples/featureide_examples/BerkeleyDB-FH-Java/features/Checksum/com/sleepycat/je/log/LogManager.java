package com.sleepycat.je.log;
abstract public class LogManager {
  static final int HEADER_CHECKSUM_OFFSET=0;
  private boolean doChecksumOnRead;
  protected static ChecksumValidator validator;
  public boolean getChecksumOnRead(){
    return doChecksumOnRead;
  }
  protected static int hook504(  int r){
    r-=CHECKSUM_BYTES;
    return original(r);
  }
  protected void hook505(  DbConfigManager configManager) throws DatabaseException {
    doChecksumOnRead=configManager.getBoolean(EnvironmentParams.LOG_CHECKSUM_READ);
    original(configManager);
  }
@MethodObject static class LogManager_getLogEntryFromLogSource {
    protected void hook506() throws DatabaseException, ClosedChannelException, Exception {
      if (_this.doChecksumOnRead) {
        validator.update(_this.envImpl,entryBuffer,itemSize,false);
        validator.validate(_this.envImpl,storedChecksum,lsn);
      }
      original();
    }
    protected void hook507() throws DatabaseException, ClosedChannelException, Exception {
      validator=null;
      storedChecksum=LogUtils.getUnsignedInt(entryBuffer);
      if (_this.doChecksumOnRead) {
        validator=new ChecksumValidator();
        validator.update(_this.envImpl,entryBuffer,_this.HEADER_CONTENT_BYTES(),false);
      }
      original();
    }
  }
}
