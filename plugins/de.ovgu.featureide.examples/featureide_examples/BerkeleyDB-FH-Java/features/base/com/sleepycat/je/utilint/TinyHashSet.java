package com.sleepycat.je.utilint;
import java.util.HashSet;
import java.util.Iterator;
import java.util.NoSuchElementException;
import java.util.Set;
import de.ovgu.cide.jakutil.*;
/** 
 * TinyHashSet is used to optimize (for speed, not space) the case where a
 * HashSet generally holds a single element.  This saves us the cost of
 * creating the HashSet and related elements as well as call Object.hashCode().
 * If single != null, it's the only element in the TinyHashSet.  If set != null
 * then there are multiple elements in the TinyHashSet.  It should never be
 * true that (single != null) && (set != null).
 */
public class TinyHashSet {
  private Set set;
  private Object single;
  public int size(){
    if (single != null) {
      return 1;
    }
 else     if (set != null) {
      return set.size();
    }
 else {
      return 0;
    }
  }
  public boolean remove(  Object o){
    assert (single == null) || (set == null);
    if (single != null) {
      if (single == o || single.equals(o)) {
        single=null;
        return true;
      }
 else {
        return false;
      }
    }
 else     if (set != null) {
      return set.remove(o);
    }
 else {
      return false;
    }
  }
  public boolean add(  Object o){
    assert (single == null) || (set == null);
    if (set != null) {
      return set.add(o);
    }
 else     if (single == null) {
      single=o;
      return true;
    }
 else {
      set=new HashSet();
      set.add(single);
      single=null;
      return set.add(o);
    }
  }
  public Set copy(){
    assert (single == null) || (set == null);
    if (set != null) {
      return new HashSet(set);
    }
 else {
      Set ret=new HashSet();
      if (single != null) {
        ret.add(single);
      }
      return ret;
    }
  }
  public Iterator iterator(){
    assert (single == null) || (set == null);
    if (set != null) {
      return set.iterator();
    }
 else {
      return new SingleElementIterator(single,this);
    }
  }
public static class SingleElementIterator implements Iterator {
    Object theObject;
    TinyHashSet theSet;
    boolean returnedTheObject=false;
    SingleElementIterator(    Object o,    TinyHashSet theSet){
      theObject=o;
      this.theSet=theSet;
      returnedTheObject=(o == null);
    }
    public boolean hasNext(){
      return !returnedTheObject;
    }
    public Object next(){
      if (returnedTheObject) {
        throw new NoSuchElementException();
      }
      returnedTheObject=true;
      return theObject;
    }
    public void remove(){
      if (theObject == null || !returnedTheObject) {
        throw new IllegalStateException();
      }
      theSet.remove(theObject);
    }
  }
}
