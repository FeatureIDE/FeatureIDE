package com.sleepycat.bind.tuple;
import com.sleepycat.bind.EntityBinding;
import com.sleepycat.je.DatabaseEntry;
import de.ovgu.cide.jakutil.*;
/** 
 * An abstract <code>EntityBinding</code> that treats an entity's key entry
 * and data entry as tuples.
 * <p>
 * This class takes care of converting the entries to/from {@link TupleInput}and {@link TupleOutput} objects. Its three abstract methods must be
 * implemented by a concrete subclass to convert between tuples and entity
 * objects.
 * </p>
 * <ul>
 * <li> {@link #entryToObject(TupleInput,TupleInput)} </li>
 * <li> {@link #objectToKey(Object,TupleOutput)} </li>
 * <li> {@link #objectToData(Object,TupleOutput)} </li>
 * </ul>
 * @author Mark Hayes
 */
public abstract class TupleTupleBinding extends TupleBase implements EntityBinding {
  /** 
 * Creates a tuple-tuple entity binding.
 */
  public TupleTupleBinding(){
  }
  public Object entryToObject(  DatabaseEntry key,  DatabaseEntry data){
    return entryToObject(TupleBinding.entryToInput(key),TupleBinding.entryToInput(data));
  }
  public void objectToKey(  Object object,  DatabaseEntry key){
    TupleOutput output=getTupleOutput(object);
    objectToKey(object,output);
    outputToEntry(output,key);
  }
  public void objectToData(  Object object,  DatabaseEntry data){
    TupleOutput output=getTupleOutput(object);
    objectToData(object,output);
    outputToEntry(output,data);
  }
  /** 
 * Constructs an entity object from {@link TupleInput} key and data entries.
 * @param keyInputis the {@link TupleInput} key entry object.
 * @param dataInputis the {@link TupleInput} data entry object.
 * @return the entity object constructed from the key and data.
 */
  public abstract Object entryToObject(  TupleInput keyInput,  TupleInput dataInput);
  /** 
 * Extracts a key tuple from an entity object.
 * @param objectis the entity object.
 * @param outputis the {@link TupleOutput} to which the key should be written.
 */
  public abstract void objectToKey(  Object object,  TupleOutput output);
  /** 
 * Extracts a key tuple from an entity object.
 * @param objectis the entity object.
 * @param outputis the {@link TupleOutput} to which the data should be
 * written.
 */
  public abstract void objectToData(  Object object,  TupleOutput output);
}
