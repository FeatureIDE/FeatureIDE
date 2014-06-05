package com.sleepycat.bind.serial;
import com.sleepycat.bind.tuple.TupleBase;
import com.sleepycat.bind.tuple.TupleInput;
import com.sleepycat.bind.tuple.TupleOutput;
import com.sleepycat.je.DatabaseEntry;
import com.sleepycat.je.DatabaseException;
import com.sleepycat.je.ForeignKeyNullifier;
import com.sleepycat.je.SecondaryDatabase;
import com.sleepycat.je.SecondaryKeyCreator;
import de.ovgu.cide.jakutil.*;
/** 
 * A abstract key creator that uses a tuple key and a serial data entry. This
 * class takes care of serializing and deserializing the data entry, and
 * converting the key entry to/from {@link TupleInput} and {@link TupleOutput}objects. The following abstract method must be implemented by a concrete
 * subclass to create the index key using these objects
 * <ul>
 * <li> {@link #createSecondaryKey(TupleInput,Object,TupleOutput)} </li>
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
public abstract class TupleSerialKeyCreator extends TupleBase implements SecondaryKeyCreator, ForeignKeyNullifier {
  protected SerialBinding dataBinding;
  /** 
 * Creates a tuple-serial key creator.
 * @param classCatalogis the catalog to hold shared class information and for a
 * database should be a {@link StoredClassCatalog}.
 * @param dataClassis the data base class.
 */
  public TupleSerialKeyCreator(  ClassCatalog classCatalog,  Class dataClass){
    this(new SerialBinding(classCatalog,dataClass));
  }
  /** 
 * Creates a tuple-serial key creator.
 * @param dataBindingis the data binding.
 */
  public TupleSerialKeyCreator(  SerialBinding dataBinding){
    this.dataBinding=dataBinding;
  }
  public boolean createSecondaryKey(  SecondaryDatabase db,  DatabaseEntry primaryKeyEntry,  DatabaseEntry dataEntry,  DatabaseEntry indexKeyEntry) throws DatabaseException {
    TupleOutput output=getTupleOutput(null);
    TupleInput primaryKeyInput=entryToInput(primaryKeyEntry);
    Object dataInput=dataBinding.entryToObject(dataEntry);
    if (createSecondaryKey(primaryKeyInput,dataInput,output)) {
      outputToEntry(output,indexKeyEntry);
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
 * Creates the index key entry from primary key tuple entry and deserialized
 * data entry.
 * @param primaryKeyInputis the {@link TupleInput} for the primary key entry, or null
 * if no primary key entry is used to construct the index key.
 * @param dataInputis the deserialized data entry, or null if no data entry is
 * used to construct the index key.
 * @param indexKeyOutputis the destination index key tuple. For index keys which are
 * optionally present, no tuple entry should be output to
 * indicate that the key is not present or null.
 * @return true if a key was created, or false to indicate that the key is
 * not present.
 */
  public abstract boolean createSecondaryKey(  TupleInput primaryKeyInput,  Object dataInput,  TupleOutput indexKeyOutput);
  /** 
 * Clears the index key in the deserialized data entry.
 * <p>
 * On entry the data parameter contains the index key to be cleared. It
 * should be changed by this method such that {@link #createSecondaryKey}will return false. Other fields in the data object should remain
 * unchanged.
 * </p>
 * @param datais the source and destination deserialized data entry.
 * @return the destination data object, or null to indicate that the key is
 * not present and no change is necessary. The data returned may be
 * the same object passed as the data parameter or a newly created
 * object.
 */
  public Object nullifyForeignKey(  Object data){
    return null;
  }
}
