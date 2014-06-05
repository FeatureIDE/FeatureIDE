package com.sleepycat.je.log;
public class FileManager {
@MethodObject static class FileManager_writeToFile {
    protected void hook455() throws IOException, DatabaseException {
      channel=file.getChannel();
      original();
    }
    protected void hook445() throws IOException, DatabaseException {
      totalBytesWritten=channel.write(data,destOffset);
      original();
    }
  }
@MethodObject static class FileManager_readFromFile {
    void execute() throws IOException {
      channel=file.getChannel();
      original();
    }
    protected void hook446() throws IOException {
      channel.read(readBuffer,offset);
      original();
    }
  }
}
