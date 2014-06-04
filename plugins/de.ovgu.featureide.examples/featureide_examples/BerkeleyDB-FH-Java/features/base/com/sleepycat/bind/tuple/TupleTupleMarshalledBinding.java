package com.sleepycat.bind.tuple;
import com.sleepycat.util.RuntimeExceptionWrapper;
import de.ovgu.cide.jakutil.*;
/** 
 * A concrete <code>TupleTupleBinding</code> that delegates to the
 * <code>MarshalledTupleEntry</code> and <code>MarshalledTupleKeyEntity</code>
 * interfaces of the entity class.
 * <p>
 * This class calls the methods of the {@link MarshalledTupleEntry} interface to
 * convert between the data entry and entity object. It calls the methods of the{@link MarshalledTupleKeyEntity} interface to convert between the key entry
 * and the entity object. These two interfaces must both be implemented by the
 * entity class.
 * </p>
 * @author Mark Hayes
 */
public class TupleTupleMarshalledBinding extends TupleTupleBinding {
  private Class cls;
  /** 
 * Creates a tuple-tuple marshalled binding object.
 * <p>
 * The given class is used to instantiate entity objects using{@link Class#forName}, and therefore must be a public class and have a
 * public no-arguments constructor. It must also implement the {@link MarshalledTupleEntry} and {@link MarshalledTupleKeyEntity} interfaces.
 * </p>
 * @param clsis the class of the entity objects.
 */
  public TupleTupleMarshalledBinding(  Class cls){
    this.cls=cls;
    if (!MarshalledTupleKeyEntity.class.isAssignableFrom(cls)) {
      throw new IllegalArgumentException(cls.toString() + " does not implement MarshalledTupleKeyEntity");
    }
    if (!MarshalledTupleEntry.class.isAssignableFrom(cls)) {
      throw new IllegalArgumentException(cls.toString() + " does not implement MarshalledTupleEntry");
    }
  }
  public Object entryToObject(  TupleInput keyInput,  TupleInput dataInput){
    MarshalledTupleEntry obj;
    try {
      obj=(MarshalledTupleEntry)cls.newInstance();
    }
 catch (    IllegalAccessException e) {
      throw new RuntimeExceptionWrapper(e);
    }
catch (    InstantiationException e) {
      throw new RuntimeExceptionWrapper(e);
    }
    if (dataInput != null) {
      obj.unmarshalEntry(dataInput);
    }
    MarshalledTupleKeyEntity entity=(MarshalledTupleKeyEntity)obj;
    if (keyInput != null) {
      entity.unmarshalPrimaryKey(keyInput);
    }
    return entity;
  }
  public void objectToKey(  Object object,  TupleOutput output){
    MarshalledTupleKeyEntity entity=(MarshalledTupleKeyEntity)object;
    entity.marshalPrimaryKey(output);
  }
  public void objectToData(  Object object,  TupleOutput output){
    MarshalledTupleEntry entity=(MarshalledTupleEntry)object;
    entity.marshalEntry(output);
  }
}
