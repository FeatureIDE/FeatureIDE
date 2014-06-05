package com.sleepycat.bind.serial;
import com.sleepycat.bind.tuple.MarshalledTupleKeyEntity;
import com.sleepycat.bind.tuple.TupleInput;
import com.sleepycat.bind.tuple.TupleOutput;
import de.ovgu.cide.jakutil.*;
/** 
 * A concrete <code>TupleSerialBinding</code> that delegates to the
 * <code>MarshalledTupleKeyEntity</code> interface of the entity class.
 * <p>
 * The {@link MarshalledTupleKeyEntity} interface must be implemented by the
 * entity class to convert between the key/data entry and entity object.
 * </p>
 * <p>
 * The binding is "tricky" in that it uses the entity class for both the stored
 * data entry and the combined entity object. To do this, the entity's key
 * field(s) are transient and are set by the binding after the data object has
 * been deserialized. This avoids the use of a "data" class completely.
 * </p>
 * @author Mark Hayes
 * @see MarshalledTupleKeyEntity
 */
public class TupleSerialMarshalledBinding extends TupleSerialBinding {
  /** 
 * Creates a tuple-serial marshalled binding object.
 * @param classCatalogis the catalog to hold shared class information and for a
 * database should be a {@link StoredClassCatalog}.
 * @param baseClassis the base class for serialized objects stored using this
 * binding -- all objects using this binding must be an instance
 * of this class.
 */
  public TupleSerialMarshalledBinding(  ClassCatalog classCatalog,  Class baseClass){
    this(new SerialBinding(classCatalog,baseClass));
  }
  /** 
 * Creates a tuple-serial marshalled binding object.
 * @param dataBindingis the binding used for serializing and deserializing the
 * entity object.
 */
  public TupleSerialMarshalledBinding(  SerialBinding dataBinding){
    super(dataBinding);
  }
  public Object entryToObject(  TupleInput tupleInput,  Object javaInput){
    MarshalledTupleKeyEntity entity=(MarshalledTupleKeyEntity)javaInput;
    if (tupleInput != null) {
      entity.unmarshalPrimaryKey(tupleInput);
    }
    return entity;
  }
  public void objectToKey(  Object object,  TupleOutput output){
    MarshalledTupleKeyEntity entity=(MarshalledTupleKeyEntity)object;
    entity.marshalPrimaryKey(output);
  }
  public Object objectToData(  Object object){
    return object;
  }
}
