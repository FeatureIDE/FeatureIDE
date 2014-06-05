package com.sleepycat.je.tree;
import com.sleepycat.je.dbi.DatabaseId;
import de.ovgu.cide.jakutil.*;
/** 
 * A class that embodies a reference to a DBIN that does not rely on a
 * java reference to the actual DBIN.
 */
public class DBINReference extends BINReference {
  private byte[] dupKey;
  DBINReference(  long nodeId,  DatabaseId databaseId,  byte[] idKey,  byte[] dupKey){
    super(nodeId,databaseId,idKey);
    this.dupKey=dupKey;
  }
  public byte[] getKey(){
    return dupKey;
  }
  public byte[] getData(){
    return idKey;
  }
  public String toString(){
    return super.toString() + " dupKey=" + Key.dumpString(dupKey,0);
  }
}
