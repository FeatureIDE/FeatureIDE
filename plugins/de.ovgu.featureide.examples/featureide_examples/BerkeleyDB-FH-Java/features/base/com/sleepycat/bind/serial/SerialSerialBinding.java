package com.sleepycat.bind.serial;
import com.sleepycat.bind.EntityBinding;
import com.sleepycat.je.DatabaseEntry;
import de.ovgu.cide.jakutil.*;
/** 
 * An abstract <code>EntityBinding</code> that treats an entity's key entry
 * and data entry as serialized objects.
 * <p>
 * This class takes care of serializing and deserializing the key and data entry
 * automatically. Its three abstract methods must be implemented by a concrete
 * subclass to convert the deserialized objects to/from an entity object.
 * </p>
 * <ul>
 * <li> {@link #entryToObject(Object,Object)} </li>
 * <li> {@link #objectToKey(Object)} </li>
 * <li> {@link #objectToData(Object)} </li>
 * </ul>
 * @author Mark Hayes
 */
public abstract class SerialSerialBinding implements EntityBinding {
  private SerialBinding keyBinding;
  private SerialBinding dataBinding;
  /** 
 * Creates a serial-serial entity binding.
 * @param classCatalogis the catalog to hold shared class information and for a
 * database should be a {@link StoredClassCatalog}.
 * @param keyClassis the key base class.
 * @param dataClassis the data base class.
 */
  public SerialSerialBinding(  ClassCatalog classCatalog,  Class keyClass,  Class dataClass){
    this(new SerialBinding(classCatalog,keyClass),new SerialBinding(classCatalog,dataClass));
  }
  /** 
 * Creates a serial-serial entity binding.
 * @param keyBindingis the key binding.
 * @param dataBindingis the data binding.
 */
  public SerialSerialBinding(  SerialBinding keyBinding,  SerialBinding dataBinding){
    this.keyBinding=keyBinding;
    this.dataBinding=dataBinding;
  }
  public Object entryToObject(  DatabaseEntry key,  DatabaseEntry data){
    return entryToObject(keyBinding.entryToObject(key),dataBinding.entryToObject(data));
  }
  public void objectToKey(  Object object,  DatabaseEntry key){
    object=objectToKey(object);
    keyBinding.objectToEntry(object,key);
  }
  public void objectToData(  Object object,  DatabaseEntry data){
    object=objectToData(object);
    dataBinding.objectToEntry(object,data);
  }
  /** 
 * Constructs an entity object from deserialized key and data objects.
 * @param keyInputis the deserialized key object.
 * @param dataInputis the deserialized data object.
 * @return the entity object constructed from the key and data.
 */
  public abstract Object entryToObject(  Object keyInput,  Object dataInput);
  /** 
 * Extracts a key object from an entity object.
 * @param objectis the entity object.
 * @return the deserialized key object.
 */
  public abstract Object objectToKey(  Object object);
  /** 
 * Extracts a data object from an entity object.
 * @param objectis the entity object.
 * @return the deserialized data object.
 */
  public abstract Object objectToData(  Object object);
}
