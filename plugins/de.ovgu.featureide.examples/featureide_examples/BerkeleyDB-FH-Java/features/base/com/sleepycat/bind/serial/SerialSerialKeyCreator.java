package com.sleepycat.bind.serial;
import com.sleepycat.je.DatabaseEntry;
import com.sleepycat.je.DatabaseException;
import com.sleepycat.je.ForeignKeyNullifier;
import com.sleepycat.je.SecondaryDatabase;
import com.sleepycat.je.SecondaryKeyCreator;
import de.ovgu.cide.jakutil.*;
/** 
 * A abstract key creator that uses a serial key and a serial data entry. This
 * class takes care of serializing and deserializing the key and data entry
 * automatically. The following abstract method must be implemented by a
 * concrete subclass to create the index key using these objects
 * <ul>
 * <li> {@link #createSecondaryKey(Object,Object)} </li>
 * </ul>
 * <!-- begin JE only -->
 * <p>
 * If {@link com.sleepycat.je.ForeignKeyDeleteAction#NULLIFY} was specified when
 * opening the secondary database, the following method must be overridden to
 * nullify the foreign index key. If NULLIFY was not specified, this method need
 * not be overridden.
 * </p>
 * <ul>
 * <li> {@link #nullifyForeignKey(Object)} </li>
 * </ul>
 * <!-- end JE only -->
 * @author Mark Hayes
 */
public abstract class SerialSerialKeyCreator implements SecondaryKeyCreator, ForeignKeyNullifier {
  protected SerialBinding primaryKeyBinding;
  protected SerialBinding dataBinding;
  protected SerialBinding indexKeyBinding;
  /** 
 * Creates a serial-serial key creator.
 * @param classCatalogis the catalog to hold shared class information and for a
 * database should be a {@link StoredClassCatalog}.
 * @param primaryKeyClassis the primary key base class.
 * @param dataClassis the data base class.
 * @param indexKeyClassis the index key base class.
 */
  public SerialSerialKeyCreator(  ClassCatalog classCatalog,  Class primaryKeyClass,  Class dataClass,  Class indexKeyClass){
    this(new SerialBinding(classCatalog,primaryKeyClass),new SerialBinding(classCatalog,dataClass),new SerialBinding(classCatalog,indexKeyClass));
  }
  /** 
 * Creates a serial-serial entity binding.
 * @param primaryKeyBindingis the primary key binding.
 * @param dataBindingis the data binding.
 * @param indexKeyBindingis the index key binding.
 */
  public SerialSerialKeyCreator(  SerialBinding primaryKeyBinding,  SerialBinding dataBinding,  SerialBinding indexKeyBinding){
    this.primaryKeyBinding=primaryKeyBinding;
    this.dataBinding=dataBinding;
    this.indexKeyBinding=indexKeyBinding;
  }
  public boolean createSecondaryKey(  SecondaryDatabase db,  DatabaseEntry primaryKeyEntry,  DatabaseEntry dataEntry,  DatabaseEntry indexKeyEntry) throws DatabaseException {
    Object primaryKeyInput=primaryKeyBinding.entryToObject(primaryKeyEntry);
    Object dataInput=dataBinding.entryToObject(dataEntry);
    Object indexKey=createSecondaryKey(primaryKeyInput,dataInput);
    if (indexKey != null) {
      indexKeyBinding.objectToEntry(indexKey,indexKeyEntry);
      return true;
    }
 else {
      return false;
    }
  }
  public boolean nullifyForeignKey(  SecondaryDatabase db,  DatabaseEntry dataEntry) throws DatabaseException {
    Object data=dataBinding.entryToObject(dataEntry);
    data=nullifyForeignKey(data);
    if (data != null) {
      dataBinding.objectToEntry(data,dataEntry);
      return true;
    }
 else {
      return false;
    }
  }
  /** 
 * Creates the index key object from primary key and entry objects.
 * @param primaryKeyis the deserialized source primary key entry, or null if no
 * primary key entry is used to construct the index key.
 * @param datais the deserialized source data entry, or null if no data
 * entry is used to construct the index key.
 * @return the destination index key object, or null to indicate that the
 * key is not present.
 */
  public abstract Object createSecondaryKey(  Object primaryKey,  Object data);
  /** 
 * Clears the index key in a data object.
 * <p>
 * On entry the data parameter contains the index key to be cleared. It
 * should be changed by this method such that {@link #createSecondaryKey}will return false. Other fields in the data object should remain
 * unchanged.
 * </p>
 * @param datais the source and destination data object.
 * @return the destination data object, or null to indicate that the key is
 * not present and no change is necessary. The data returned may be
 * the same object passed as the data parameter or a newly created
 * object.
 */
  public Object nullifyForeignKey(  Object data){
    return null;
  }
}
