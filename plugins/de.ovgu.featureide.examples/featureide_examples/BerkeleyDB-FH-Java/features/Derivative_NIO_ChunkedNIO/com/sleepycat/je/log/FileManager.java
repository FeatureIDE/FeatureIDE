package com.sleepycat.je.log;
public class FileManager {
@MethodObject static class FileManager_writeToFile {
    protected void hook445() throws IOException, DatabaseException {
      if (_this.chunkedNIOSize > 0) {
        useData=data.duplicate();
        origLimit=useData.limit();
        useData.limit(useData.position());
        while (useData.limit() < origLimit) {
          useData.limit((int)(Math.min(useData.limit() + _this.chunkedNIOSize,origLimit)));
          bytesWritten=channel.write(useData,destOffset);
          destOffset+=bytesWritten;
          totalBytesWritten+=bytesWritten;
        }
      }
 else {
        original();
      }
    }
  }
@MethodObject static class FileManager_readFromFile {
    protected void hook446() throws IOException {
      if (_this.chunkedNIOSize > 0) {
        readLength=readBuffer.limit();
        currentPosition=offset;
        while (readBuffer.position() < readLength) {
          readBuffer.limit((int)(Math.min(readBuffer.limit() + _this.chunkedNIOSize,readLength)));
          bytesRead1=channel.read(readBuffer,currentPosition);
          if (bytesRead1 < 1)           break;
          currentPosition+=bytesRead1;
        }
      }
 else {
        original();
      }
    }
  }
}
