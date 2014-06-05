package com.sleepycat.je.log;
import java.nio.ByteBuffer;
import java.util.zip.Checksum;
import com.sleepycat.je.dbi.EnvironmentImpl;
import com.sleepycat.je.utilint.Adler32;
import com.sleepycat.je.utilint.DbLsn;
import de.ovgu.cide.jakutil.*;
/** 
 * Checksum validator is used to check checksums on log entries.
 */
class ChecksumValidator {
  private static final boolean DEBUG=false;
  private Checksum cksum;
  ChecksumValidator(){
    cksum=Adler32.makeChecksum();
  }
  void reset(){
    cksum.reset();
  }
  /** 
 * Add this byte buffer to the checksum. Assume the byte buffer is already
 * positioned at the data.
 * @param buf target buffer
 * @param length of data
 */
  void update(  EnvironmentImpl env,  ByteBuffer buf,  int length,  boolean anticipateChecksumErrors) throws DbChecksumException {
    if (buf == null) {
      throw new DbChecksumException((anticipateChecksumErrors ? null : env),"null buffer given to checksum validation, probably " + " result of 0's in log file. " + anticipateChecksumErrors);
    }
    int bufStart=buf.position();
    if (DEBUG) {
      System.out.println("bufStart = " + bufStart + " length = "+ length);
    }
    if (buf.hasArray()) {
      cksum.update(buf.array(),bufStart,length);
    }
 else {
      for (int i=bufStart; i < (length + bufStart); i++) {
        cksum.update(buf.get(i));
      }
    }
  }
  void validate(  EnvironmentImpl env,  long expectedChecksum,  long lsn) throws DbChecksumException {
    if (expectedChecksum != cksum.getValue()) {
      throw new DbChecksumException(env,"Location " + DbLsn.getNoFormatString(lsn) + " expected "+ expectedChecksum+ " got "+ cksum.getValue());
    }
  }
  void validate(  EnvironmentImpl env,  long expectedChecksum,  long fileNum,  long fileOffset,  boolean anticipateChecksumErrors) throws DbChecksumException {
    if (expectedChecksum != cksum.getValue()) {
      long problemLsn=DbLsn.makeLsn(fileNum,fileOffset);
      throw new DbChecksumException((anticipateChecksumErrors ? null : env),"Location " + DbLsn.getNoFormatString(problemLsn) + " expected "+ expectedChecksum+ " got "+ cksum.getValue());
    }
  }
}
