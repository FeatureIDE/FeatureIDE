package com.sleepycat.je.utilint;
import java.util.HashSet;
import java.util.Set;
import java.util.TreeMap;
import com.sleepycat.je.tree.IN;
import de.ovgu.cide.jakutil.*;
/** 
 * A level ordered map holds collection of INs, sorted by level. The map is
 * keyed by level and each datum is a set of INs belonging to that level.
 */
public class LevelOrderedINMap extends TreeMap {
  public void putIN(  IN in){
    Integer level=new Integer(in.getLevel());
    Set inSet=(Set)get(level);
    if (inSet == null) {
      inSet=new HashSet();
      put(level,inSet);
    }
    inSet.add(in);
  }
}
