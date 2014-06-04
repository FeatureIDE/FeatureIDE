package com.sleepycat.je.log;
public class FileManager {
@MethodObject static class FileManager_writeToFile {
    protected void hook447() throws IOException, DatabaseException {
      assert data.hasArray();
      assert data.arrayOffset() == 0;
      pos=data.position();
      size=data.limit() - pos;
      file.seek(destOffset);
      file.write(data.array(),pos,size);
      data.position(pos + size);
      totalBytesWritten=size;
    }
    int execute() throws IOException, DatabaseException {
      int result=original();
{
        this.hook447();
      }
      return result;
    }
  }
@MethodObject static class FileManager_readFromFile {
    protected void hook448() throws IOException {
      assert readBuffer.hasArray();
      assert readBuffer.arrayOffset() == 0;
      pos=readBuffer.position();
      size=readBuffer.limit() - pos;
      file.seek(offset);
      bytesRead2=file.read(readBuffer.array(),pos,size);
      if (bytesRead2 > 0) {
        readBuffer.position(pos + bytesRead2);
      }
    }
    void execute() throws IOException {
      original();
{
        this.hook448();
      }
    }
  }
}
