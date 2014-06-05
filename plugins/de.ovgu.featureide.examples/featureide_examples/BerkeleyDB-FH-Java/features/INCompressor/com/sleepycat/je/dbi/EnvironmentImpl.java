package com.sleepycat.je.dbi;
import com.sleepycat.je.incomp.INCompressor;
public class EnvironmentImpl {
  private INCompressor inCompressor;
  /** 
 * Return the incompressor. In general, don't use this directly because it's
 * easy to forget that the incompressor can be null at times (i.e during the
 * shutdown procedure. Instead, wrap the functionality within this class,
 * like lazyCompress.
 */
  public INCompressor getINCompressor(){
    return inCompressor;
  }
  /** 
 * Tells the asynchronous IN compressor thread about a BIN with a deleted
 * entry.
 */
  public void addToCompressorQueue(  BIN bin,  Key deletedKey,  boolean doWakeup) throws DatabaseException {
    if (inCompressor != null) {
      inCompressor.addBinKeyToQueue(bin,deletedKey,doWakeup);
    }
  }
  /** 
 * Tells the asynchronous IN compressor thread about a BINReference with a
 * deleted entry.
 */
  public void addToCompressorQueue(  BINReference binRef,  boolean doWakeup) throws DatabaseException {
    if (inCompressor != null) {
      inCompressor.addBinRefToQueue(binRef,doWakeup);
    }
  }
  /** 
 * Tells the asynchronous IN compressor thread about a collections of
 * BINReferences with deleted entries.
 */
  public void addToCompressorQueue(  Collection binRefs,  boolean doWakeup) throws DatabaseException {
    if (inCompressor != null) {
      inCompressor.addMultipleBinRefsToQueue(binRefs,doWakeup);
    }
  }
  /** 
 * Do lazy compression at opportune moments.
 */
  public void lazyCompress(  IN in) throws DatabaseException {
    if (inCompressor != null) {
      inCompressor.lazyCompress(in);
    }
  }
  /** 
 * Invoke a compress programatically. Note that only one compress may run at
 * a time.
 */
  public boolean invokeCompressor() throws DatabaseException {
    if (inCompressor != null) {
      inCompressor.doCompress();
      return true;
    }
 else {
      return false;
    }
  }
  /** 
 * Available for the unit tests.
 */
  public void shutdownINCompressor() throws InterruptedException {
    if (inCompressor != null) {
      inCompressor.shutdown();
      inCompressor.clearEnv();
      inCompressor=null;
    }
    return;
  }
  public int getINCompressorQueueSize() throws DatabaseException {
    return inCompressor.getBinRefQueueSize();
  }
  protected void hook330(  DbConfigManager mgr) throws DatabaseException {
    inCompressor.runOrPause(mgr.getBoolean(EnvironmentParams.ENV_RUN_INCOMPRESSOR));
    original(mgr);
  }
  protected void hook331(){
    if (inCompressor != null) {
      inCompressor.requestShutdown();
    }
    original();
  }
  /** 
 * Ask all daemon threads to shut down.
 */
  private void shutdownDaemons() throws InterruptedException {
    shutdownINCompressor();
    original();
  }
@MethodObject static class EnvironmentImpl_createDaemons {
    protected void hook332() throws DatabaseException {
      compressorWakeupInterval=PropUtil.microsToMillis(_this.configManager.getLong(EnvironmentParams.COMPRESSOR_WAKEUP_INTERVAL));
      _this.inCompressor=new INCompressor(_this,compressorWakeupInterval,"INCompressor");
      original();
    }
  }
}
