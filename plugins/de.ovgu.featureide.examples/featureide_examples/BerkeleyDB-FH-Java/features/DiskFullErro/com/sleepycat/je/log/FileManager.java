package com.sleepycat.je.log;
public class FileManager {
  protected void hook465(  LogBuffer fullBuffer,  long firstLsn,  RandomAccessFile file) throws DatabaseException, ClosedChannelException, IOException {
    assert fullBuffer.getRewriteAllowed() || (DbLsn.getFileOffset(firstLsn) >= file.length() || file.length() == firstLogEntryOffset()) : "FileManager would overwrite non-empty file 0x" + Long.toHexString(DbLsn.getFileNumber(firstLsn)) + " lsnOffset=0x"+ Long.toHexString(DbLsn.getFileOffset(firstLsn))+ " fileLength=0x"+ Long.toHexString(file.length());
    original(fullBuffer,firstLsn,file);
  }
  protected void hook466(  LogBuffer fullBuffer,  long firstLsn,  RandomAccessFile file,  ByteBuffer data,  IOException IOE) throws DatabaseException {
    try {
      if (IO_EXCEPTION_TESTING) {
        throw new IOException("generated for testing");
      }
      writeToFile(file,data,DbLsn.getFileOffset(firstLsn));
    }
 catch (    IOException IOE2) {
      fullBuffer.setRewriteAllowed();
      throw new DatabaseException(IOE2);
    }
    if (false)     original(fullBuffer,firstLsn,file,data,IOE);
  }
}
