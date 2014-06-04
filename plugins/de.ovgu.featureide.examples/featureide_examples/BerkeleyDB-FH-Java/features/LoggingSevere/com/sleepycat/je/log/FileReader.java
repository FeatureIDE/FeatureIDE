package com.sleepycat.je.log;
public abstract class FileReader {
@MethodObject static class FileReader_readNextEntry {
    protected void hook468() throws DatabaseException, IOException {
      _this.eof=true;
      problemType=LogEntryType.findType(_this.currentEntryTypeNum,_this.currentEntryTypeVersion);
      Tracer.trace(_this.env,"FileReader","readNextEntry","Halted log file reading at file 0x" + Long.toHexString(_this.readBufferFileNum) + " offset 0x"+ Long.toHexString(_this.nextEntryOffset)+ " offset(decimal)="+ _this.nextEntryOffset+ ":\nentry="+ problemType+ "(typeNum="+ _this.currentEntryTypeNum+ ",version="+ _this.currentEntryTypeVersion+ ")\nprev=0x"+ Long.toHexString(_this.currentEntryPrevOffset)+ "\nsize="+ _this.currentEntrySize+ "\nNext entry should be at 0x"+ Long.toHexString((_this.nextEntryOffset + LogManager.HEADER_BYTES + _this.currentEntrySize))+ "\n:",e);
      original();
    }
  }
}
