package com.sleepycat.je.log;
public abstract class FileReader {
  protected ChecksumValidator cksumValidator;
  private boolean doValidateChecksum;
  private boolean alwaysValidateChecksum;
  /** 
 * Whether to always validate the checksum, even for non-target entries.
 */
  public void setAlwaysValidateChecksum(  boolean validate){
    alwaysValidateChecksum=validate;
  }
  /** 
 * Reset the checksum and add the header bytes. This method must be called
 * with the entry header data at the buffer mark.
 */
  private void startChecksum(  ByteBuffer dataBuffer) throws DatabaseException {
    cksumValidator.reset();
    int entryStart=threadSafeBufferPosition(dataBuffer);
    dataBuffer.reset();
    cksumValidator.update(env,dataBuffer,LogManager.HEADER_CONTENT_BYTES(),anticipateChecksumErrors);
    threadSafeBufferPosition(dataBuffer,entryStart);
  }
  /** 
 * Add the entry bytes to the checksum and check the value. This method must
 * be called with the buffer positioned at the start of the entry.
 */
  private void validateChecksum(  ByteBuffer entryBuffer) throws DatabaseException {
    cksumValidator.update(env,entryBuffer,currentEntrySize,anticipateChecksumErrors);
    cksumValidator.validate(env,currentEntryChecksum,readBufferFileNum,currentEntryOffset,anticipateChecksumErrors);
  }
  protected void hook472() throws IOException, DatabaseException {
    if (doValidateChecksum) {
      cksumValidator=new ChecksumValidator();
    }
    original();
  }
  protected void hook473(  EnvironmentImpl env) throws IOException, DatabaseException {
    this.doValidateChecksum=env.getLogManager().getChecksumOnRead();
    original(env);
  }
@MethodObject static class FileReader_readNextEntry {
    protected void hook474() throws DatabaseException, IOException, EOFException {
      if (doValidate) {
        _this.validateChecksum(dataBuffer);
      }
      original();
    }
    protected void hook475() throws DatabaseException, IOException, EOFException {
      collectData|=doValidate;
      if (doValidate) {
        _this.startChecksum(dataBuffer);
      }
      original();
    }
    protected void hook476() throws DatabaseException, IOException, EOFException {
      doValidate=_this.doValidateChecksum && (isTargetEntry || _this.alwaysValidateChecksum);
      original();
    }
  }
}
