package com.sleepycat.je.cleaner;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;
import com.sleepycat.je.Database;
import com.sleepycat.je.DatabaseException;
import com.sleepycat.je.DbInternal;
import com.sleepycat.je.dbi.DatabaseImpl;
import com.sleepycat.je.dbi.SortedLSNTreeWalker;
import com.sleepycat.je.dbi.SortedLSNTreeWalker.TreeNodeProcessor;
import com.sleepycat.je.log.LogEntryType;
import com.sleepycat.je.utilint.DbLsn;
import de.ovgu.cide.jakutil.*;
/** 
 * Verify cleaner data structures
 */
public class VerifyUtils {
  private static final boolean DEBUG=false;
  /** 
 * Compare the lsns referenced by a given Database to the lsns held
 * in the utilization profile. Assumes that the database and
 * environment is quiescent, and that there is no current cleaner
 * activity.
 */
  public static void checkLsns(  Database db) throws DatabaseException {
    DatabaseImpl dbImpl=DbInternal.dbGetDatabaseImpl(db);
    GatherLSNs gatherLsns=new GatherLSNs();
    long rootLsn=dbImpl.getTree().getRootLsn();
    SortedLSNTreeWalker walker=new SortedLSNTreeWalker(dbImpl,false,false,rootLsn,gatherLsns);
    walker.walk();
    Set lsnsInTree=gatherLsns.getLsns();
    lsnsInTree.add(new Long(rootLsn));
    Iterator iter=lsnsInTree.iterator();
    Set fileNums=new HashSet();
    while (iter.hasNext()) {
      long lsn=((Long)iter.next()).longValue();
      fileNums.add(new Long(DbLsn.getFileNumber(lsn)));
    }
    iter=fileNums.iterator();
    Set obsoleteLsns=new HashSet();
    UtilizationProfile profile=dbImpl.getDbEnvironment().getUtilizationProfile();
    while (iter.hasNext()) {
      Long fileNum=(Long)iter.next();
      PackedOffsets obsoleteOffsets=new PackedOffsets();
      TrackedFileSummary tfs=profile.getObsoleteDetail(fileNum,obsoleteOffsets,false);
      PackedOffsets.Iterator obsoleteIter=obsoleteOffsets.iterator();
      while (obsoleteIter.hasNext()) {
        long offset=obsoleteIter.next();
        Long oneLsn=new Long(DbLsn.makeLsn(fileNum.longValue(),offset));
        obsoleteLsns.add(oneLsn);
        if (DEBUG) {
          System.out.println("Adding 0x" + Long.toHexString(oneLsn.longValue()));
        }
      }
    }
    boolean error=false;
    iter=lsnsInTree.iterator();
    while (iter.hasNext()) {
      Long lsn=(Long)iter.next();
      if (obsoleteLsns.contains(lsn)) {
        System.err.println("Obsolete lsns contains valid lsn " + DbLsn.getNoFormatString(lsn.longValue()));
        error=true;
      }
    }
    iter=obsoleteLsns.iterator();
    while (iter.hasNext()) {
      Long lsn=(Long)iter.next();
      if (lsnsInTree.contains(lsn)) {
        System.err.println("Tree contains obsolete lsn " + DbLsn.getNoFormatString(lsn.longValue()));
        error=true;
      }
    }
    if (error) {
      throw new DatabaseException("Lsn mismatch");
    }
  }
private static class GatherLSNs implements TreeNodeProcessor {
    private Set lsns=new HashSet();
    public void processLSN(    long childLSN,    LogEntryType childType){
      lsns.add(new Long(childLSN));
    }
    public Set getLsns(){
      return lsns;
    }
  }
}
