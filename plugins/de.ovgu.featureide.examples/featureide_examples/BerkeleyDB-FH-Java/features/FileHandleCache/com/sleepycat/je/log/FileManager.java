package com.sleepycat.je.log;
public class FileManager {
  private FileCache fileCache;
  Set getCacheKeys(){
    return fileCache.getCacheKeys();
  }
  /** 
 * Clear a file out of the file cache regardless of mode type.
 */
  private void clearFileCache(  long fileNum) throws IOException, DatabaseException {
    fileCache.remove(fileNum);
  }
  protected void hook451() throws IOException, DatabaseException {
    fileCache.clear();
  }
  protected void hook457(  DbConfigManager configManager) throws DatabaseException {
    fileCache=new FileCache(configManager);
    original(configManager);
  }
  protected void hook458(  long fileNum) throws DatabaseException, IOException {
    clearFileCache(fileNum);
    original(fileNum);
  }
  protected void hook459(  long fileNum) throws DatabaseException, IOException {
    clearFileCache(fileNum);
    original(fileNum);
  }
  protected void hook460(  long fileNum,  Long fileId,  FileHandle fileHandle) throws LogException, DatabaseException {
    while (true) {
      original(fileNum,fileId,fileHandle);
    }
  }
  protected void hook461(  ByteBuffer data){
    data.position(0);
    original(data);
  }
  /** 
 * Close all file handles and empty the cache.
 */
  public void clear() throws IOException, DatabaseException {
{
      this.hook451();
    }
    original();
  }
  protected FileHandle hook462(  long fileNum,  Long fileId,  FileHandle fileHandle) throws LogException, DatabaseException {
    fileHandle=fileCache.get(fileId);
    if (fileHandle == null) {
      fileHandle=original(fileNum,fileId,fileHandle);
    }
    return fileHandle;
  }
  protected FileHandle hook463(  long fileNum,  Long fileId,  FileHandle fileHandle) throws LogException, DatabaseException {
    fileHandle=fileCache.get(fileId);
    if (fileHandle == null) {
      fileHandle=original(fileNum,fileId,fileHandle);
    }
    return fileHandle;
  }
  protected void hook464(  Long fileId,  FileHandle fileHandle) throws LogException, DatabaseException {
    fileCache.add(fileId,fileHandle);
    original(fileId,fileHandle);
  }
}
