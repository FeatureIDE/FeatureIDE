package com.sleepycat.je.log;
import java.io.IOException;
import java.util.Hashtable;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.Map;
import java.util.Set;
import com.sleepycat.je.DatabaseException;
import com.sleepycat.je.config.EnvironmentParams;
import com.sleepycat.je.dbi.DbConfigManager;
import de.ovgu.cide.jakutil.*;
class FileCache {
  private Map fileMap;
  private LinkedList fileList;
  private int fileCacheSize;
  FileCache(  DbConfigManager configManager) throws DatabaseException {
    fileMap=new Hashtable();
    fileList=new LinkedList();
    fileCacheSize=configManager.getInt(EnvironmentParams.LOG_FILE_CACHE_SIZE);
  }
  FileHandle get(  Long fileId){
    return (FileHandle)fileMap.get(fileId);
  }
  void add(  Long fileId,  FileHandle fileHandle) throws DatabaseException {
    if (fileList.size() >= fileCacheSize) {
      Iterator iter=fileList.iterator();
      boolean done=false;
      while (!done && iter.hasNext()) {
        Long evictId=(Long)iter.next();
        FileHandle evictTarget=(FileHandle)fileMap.get(evictId);
        this.hook438(iter,done,evictId,evictTarget);
      }
    }
    fileList.add(fileId);
    fileMap.put(fileId,fileHandle);
  }
  /** 
 * Take any file handles corresponding to this file name out of the cache. A
 * file handle could be there twice, in rd only and in r/w mode.
 */
  void remove(  long fileNum) throws IOException, DatabaseException {
    Iterator iter=fileList.iterator();
    while (iter.hasNext()) {
      Long evictId=(Long)iter.next();
      if (evictId.longValue() == fileNum) {
        FileHandle evictTarget=(FileHandle)fileMap.get(evictId);
        this.hook439(iter,evictId,evictTarget);
      }
    }
  }
  void clear() throws IOException, DatabaseException {
    Iterator iter=fileMap.values().iterator();
    while (iter.hasNext()) {
      FileHandle fileHandle=(FileHandle)iter.next();
      this.hook440(iter,fileHandle);
    }
    fileMap.clear();
    fileList.clear();
  }
  Set getCacheKeys(){
    return fileMap.keySet();
  }
  protected void hook438(  Iterator iter,  boolean done,  Long evictId,  FileHandle evictTarget) throws DatabaseException {
    try {
      fileMap.remove(evictId);
      iter.remove();
      evictTarget.close();
    }
 catch (    IOException e) {
      throw new DatabaseException(e);
    }
 finally {
      this.hook441(evictTarget);
    }
    done=true;
  }
  protected void hook439(  Iterator iter,  Long evictId,  FileHandle evictTarget) throws IOException, DatabaseException {
    this.hook442(evictTarget);
    fileMap.remove(evictId);
    iter.remove();
    evictTarget.close();
  }
  protected void hook440(  Iterator iter,  FileHandle fileHandle) throws IOException, DatabaseException {
    this.hook443(fileHandle);
    fileHandle.close();
    iter.remove();
  }
  protected void hook441(  FileHandle evictTarget) throws DatabaseException {
  }
  protected void hook442(  FileHandle evictTarget) throws IOException, DatabaseException {
  }
  protected void hook443(  FileHandle fileHandle) throws IOException, DatabaseException {
  }
}
