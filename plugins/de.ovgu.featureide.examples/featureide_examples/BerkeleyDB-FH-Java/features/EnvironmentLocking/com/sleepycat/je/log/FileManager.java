package com.sleepycat.je.log;
public class FileManager {
  private RandomAccessFile lockFile;
  private FileChannel channel;
  private FileLock envLock;
  private FileLock exclLock;
  /** 
 * Lock the environment. Return true if the lock was acquired. If exclusive
 * is false, then this implements a single writer, multiple reader lock. If
 * exclusive is true, then implement an exclusive lock.
 * There is a lock file and there are two regions of the lock file: byte 0,
 * and byte 1. Byte 0 is the exclusive writer process area of the lock file.
 * If an environment is opened for write, then it attempts to take an
 * exclusive write lock on byte 0. Byte 1 is the shared reader process area
 * of the lock file. If an environment is opened for read-only, then it
 * attempts to take a shared lock on byte 1. This is how we implement single
 * writer, multi reader semantics.
 * The cleaner, each time it is invoked, attempts to take an exclusive lock
 * on byte 1. The owning process already either has an exclusive lock on
 * byte 0, or a shared lock on byte 1. This will necessarily conflict with
 * any shared locks on byte 1, even if it's in the same process and there
 * are no other holders of that shared lock. So if there is only one
 * read-only process, it will have byte 1 for shared access, and the cleaner
 * can not run in it because it will attempt to get an exclusive lock on
 * byte 1 (which is already locked for shared access by itself). If a write
 * process comes along and tries to run the cleaner, it will attempt to get
 * an exclusive lock on byte 1. If there are no other reader processes (with
 * shared locks on byte 1), and no other writers (which are running cleaners
 * on with exclusive locks on byte 1), then the cleaner will run.
 */
  public boolean lockEnvironment(  boolean readOnly,  boolean exclusive) throws DatabaseException {
    try {
      if (checkEnvHomePermissions(readOnly)) {
        return true;
      }
      if (lockFile == null) {
        lockFile=new RandomAccessFile(new File(dbEnvHome,"je" + LOCK_SUFFIX),"rw");
      }
      channel=lockFile.getChannel();
      boolean throwIt=false;
      try {
        if (exclusive) {
          exclLock=channel.tryLock(1,2,false);
          if (exclLock == null) {
            return false;
          }
          return true;
        }
 else {
          if (readOnly) {
            envLock=channel.tryLock(1,2,true);
          }
 else {
            envLock=channel.tryLock(0,1,false);
          }
          if (envLock == null) {
            throwIt=true;
          }
        }
      }
 catch (      OverlappingFileLockException e) {
        throwIt=true;
      }
      if (throwIt) {
        throw new LogException("A je" + LOCK_SUFFIX + "file exists in "+ dbEnvHome+ " The environment can not be locked for "+ (readOnly ? "shared" : "single writer")+ " access.");
      }
    }
 catch (    IOException IOE) {
      throw new LogException(IOE.toString());
    }
    return true;
  }
  public void releaseExclusiveLock() throws DatabaseException {
    try {
      if (exclLock != null) {
        exclLock.release();
      }
    }
 catch (    IOException IOE) {
      throw new DatabaseException(IOE);
    }
  }
  protected void hook467(  boolean readOnly) throws DatabaseException {
    lockEnvironment(readOnly,false);
    original(readOnly);
  }
  /** 
 * Clear the file lock.
 */
  public void close() throws IOException, DatabaseException {
    if (envLock != null) {
      envLock.release();
    }
    if (exclLock != null) {
      exclLock.release();
    }
    if (channel != null) {
      channel.close();
    }
    if (lockFile != null) {
      lockFile.close();
    }
    original();
  }
}
