package com.sleepycat.je.log.entry;
import com.sleepycat.je.DatabaseException;
import com.sleepycat.je.dbi.DatabaseId;
import com.sleepycat.je.dbi.EnvironmentImpl;
import com.sleepycat.je.tree.BINDelta;
import com.sleepycat.je.tree.IN;
import de.ovgu.cide.jakutil.*;
/** 
 * A BINDeltaLogEntry knows how to create a whole BIN from a delta entry.
 */
public class BINDeltaLogEntry extends SingleItemLogEntry implements INContainingEntry {
  /** 
 * @param logClass
 */
  public BINDeltaLogEntry(  Class logClass){
    super(logClass);
  }
  public IN getIN(  EnvironmentImpl env) throws DatabaseException {
    BINDelta delta=(BINDelta)getMainItem();
    return delta.reconstituteBIN(env);
  }
  public DatabaseId getDbId(){
    BINDelta delta=(BINDelta)getMainItem();
    return delta.getDbId();
  }
  /** 
 * @return the LSN that represents this IN. For this BINDelta, it's
 * the last full version.
 */
  public long getLsnOfIN(  long lastReadLsn){
    BINDelta delta=(BINDelta)getMainItem();
    return delta.getLastFullLsn();
  }
}
