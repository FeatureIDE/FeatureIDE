package com.sleepycat.je.log;
import java.io.IOException;
import java.nio.ByteBuffer;
import java.util.List;
import com.sleepycat.je.DatabaseException;
import com.sleepycat.je.cleaner.TrackedFileSummary;
import com.sleepycat.je.cleaner.UtilizationTracker;
import com.sleepycat.je.dbi.EnvironmentImpl;
import de.ovgu.cide.jakutil.*;
/** 
 * The LatchedLogManager uses the latches to implement critical sections.
 */
public class LatchedLogManager extends LogManager {
  /** 
 * There is a single log manager per database environment.
 */
  public LatchedLogManager(  EnvironmentImpl envImpl,  boolean readOnly) throws DatabaseException {
    super(envImpl,readOnly);
  }
  protected LogResult logItem(  LoggableObject item,  boolean isProvisional,  boolean flushRequired,  boolean forceNewLogFile,  long oldNodeLsn,  boolean marshallOutsideLatch,  ByteBuffer marshalledBuffer,  UtilizationTracker tracker) throws IOException, DatabaseException {
    logWriteLatch.acquire();
    try {
      return logInternal(item,isProvisional,flushRequired,forceNewLogFile,oldNodeLsn,marshallOutsideLatch,marshalledBuffer,tracker);
    }
  finally {
      logWriteLatch.release();
    }
  }
  protected void flushInternal() throws LogException, DatabaseException {
    logWriteLatch.acquire();
    try {
      logBufferPool.writeBufferToFile(0);
    }
 catch (    IOException e) {
      throw new LogException(e.getMessage());
    }
 finally {
      logWriteLatch.release();
    }
  }
  /** 
 * @see LogManager#getUnflusableTrackedSummary
 */
  public TrackedFileSummary getUnflushableTrackedSummary(  long file) throws DatabaseException {
    logWriteLatch.acquire();
    try {
      return getUnflushableTrackedSummaryInternal(file);
    }
  finally {
      logWriteLatch.release();
    }
  }
  /** 
 * @see LogManager#countObsoleteLNs
 */
  public void countObsoleteNode(  long lsn,  LogEntryType type) throws DatabaseException {
    UtilizationTracker tracker=envImpl.getUtilizationTracker();
    logWriteLatch.acquire();
    try {
      countObsoleteNodeInternal(tracker,lsn,type);
    }
  finally {
      logWriteLatch.release();
    }
  }
  /** 
 * @see LogManager#countObsoleteNodes
 */
  public void countObsoleteNodes(  TrackedFileSummary[] summaries) throws DatabaseException {
    UtilizationTracker tracker=envImpl.getUtilizationTracker();
    logWriteLatch.acquire();
    try {
      countObsoleteNodesInternal(tracker,summaries);
    }
  finally {
      logWriteLatch.release();
    }
  }
  /** 
 * @see LogManager#countObsoleteINs
 */
  public void countObsoleteINs(  List lsnList) throws DatabaseException {
    logWriteLatch.acquire();
    try {
      countObsoleteINsInternal(lsnList);
    }
  finally {
      logWriteLatch.release();
    }
  }
}
