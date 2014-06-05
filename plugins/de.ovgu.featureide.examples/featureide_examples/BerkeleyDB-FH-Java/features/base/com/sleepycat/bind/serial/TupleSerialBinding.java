package com.sleepycat.bind.serial;
import com.sleepycat.bind.EntityBinding;
import com.sleepycat.bind.tuple.TupleBase;
import com.sleepycat.bind.tuple.TupleInput;
import com.sleepycat.bind.tuple.TupleOutput;
import com.sleepycat.je.DatabaseEntry;
import de.ovgu.cide.jakutil.*;
/** 
 * An abstract <code>EntityBinding</code> that treats an entity's key entry as
 * a tuple and its data entry as a serialized object.
 * <p>
 * This class takes care of serializing and deserializing the data entry, and
 * converting the key entry to/from {@link TupleInput} and {@link TupleOutput}objects. Its three abstract methods must be implemented by a concrete
 * subclass to convert these objects to/from an entity object.
 * </p>
 * <ul>
 * <li> {@link #entryToObject(TupleInput,Object)} </li>
 * <li> {@link #objectToKey(Object,TupleOutput)} </li>
 * <li> {@link #objectToData(Object)} </li>
 * </ul>
 * @author Mark Hayes
 */
public abstract class TupleSerialBinding extends TupleBase implements EntityBinding {
  protected SerialBinding dataBinding;
  /** 
 * Creates a tuple-serial entity binding.
 * @param classCatalogis the catalog to hold shared class information and for a
 * database should be a {@link StoredClassCatalog}.
 * @param baseClassis the base class.
 */
  public TupleSerialBinding(  ClassCatalog classCatalog,  Class baseClass){
    this(new SerialBinding(classCatalog,baseClass));
  }
  /** 
 * Creates a tuple-serial entity binding.
 * @param dataBindingis the data binding.
 */
  public TupleSerialBinding(  SerialBinding dataBinding){
    this.dataBinding=dataBinding;
  }
  public Object entryToObject(  DatabaseEntry key,  DatabaseEntry data){
    return entryToObject(entryToInput(key),dataBinding.entryToObject(data));
  }
  public void objectToKey(  Object object,  DatabaseEntry key){
    TupleOutput output=getTupleOutput(object);
    objectToKey(object,output);
    outputToEntry(output,key);
  }
  public void objectToData(  Object object,  DatabaseEntry data){
    object=objectToData(object);
    dataBinding.objectToEntry(object,data);
  }
  /** 
 * Constructs an entity object from {@link TupleInput} key entry and
 * deserialized data entry objects.
 * @param keyInputis the {@link TupleInput} key entry object.
 * @param dataInputis the deserialized data entry object.
 * @return the entity object constructed from the key and data.
 */
  public abstract Object entryToObject(  TupleInput keyInput,  Object dataInput);
  /** 
 * Extracts a key tuple from an entity object.
 * @param objectis the entity object.
 * @param keyOutputis the {@link TupleOutput} to which the key should be written.
 */
  public abstract void objectToKey(  Object object,  TupleOutput keyOutput);
  /** 
 * Extracts a data object from an entity object.
 * @param objectis the entity object.
 * @return the deserialized data object.
 */
  public abstract Object objectToData(  Object object);
}
