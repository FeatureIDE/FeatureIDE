package com.sleepycat.je.tree;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;
import com.sleepycat.je.dbi.DatabaseId;
import de.ovgu.cide.jakutil.*;
/** 
 * A class that embodies a reference to a BIN that does not rely on a
 * Java reference to the actual BIN.
 */
public class BINReference {
  protected byte[] idKey;
  private long nodeId;
  private DatabaseId databaseId;
  private Set deletedKeys;
  BINReference(  long nodeId,  DatabaseId databaseId,  byte[] idKey){
    this.nodeId=nodeId;
    this.databaseId=databaseId;
    this.idKey=idKey;
  }
  public long getNodeId(){
    return nodeId;
  }
  public DatabaseId getDatabaseId(){
    return databaseId;
  }
  public byte[] getKey(){
    return idKey;
  }
  public byte[] getData(){
    return null;
  }
  public void addDeletedKey(  Key key){
    if (deletedKeys == null) {
      deletedKeys=new HashSet();
    }
    deletedKeys.add(key);
  }
  public void addDeletedKeys(  BINReference other){
    if (deletedKeys == null) {
      deletedKeys=new HashSet();
    }
    if (other.deletedKeys != null) {
      deletedKeys.addAll(other.deletedKeys);
    }
  }
  public void removeDeletedKey(  Key key){
    if (deletedKeys != null) {
      deletedKeys.remove(key);
      if (deletedKeys.size() == 0) {
        deletedKeys=null;
      }
    }
  }
  public boolean hasDeletedKey(  Key key){
    return (deletedKeys != null) && deletedKeys.contains(key);
  }
  public boolean deletedKeysExist(){
    return ((deletedKeys != null) && (deletedKeys.size() > 0));
  }
  public Iterator getDeletedKeyIterator(){
    if (deletedKeys != null) {
      return deletedKeys.iterator();
    }
 else {
      return null;
    }
  }
  /** 
 * Compare two BINReferences.
 */
  public boolean equals(  Object obj){
    if (this == obj) {
      return true;
    }
    if (!(obj instanceof BINReference)) {
      return false;
    }
    return ((BINReference)obj).nodeId == nodeId;
  }
  public int hashCode(){
    return (int)nodeId;
  }
  public String toString(){
    return "idKey=" + Key.getNoFormatString(idKey) + " nodeId = "+ nodeId+ " db="+ databaseId+ " deletedKeys="+ deletedKeys;
  }
}
