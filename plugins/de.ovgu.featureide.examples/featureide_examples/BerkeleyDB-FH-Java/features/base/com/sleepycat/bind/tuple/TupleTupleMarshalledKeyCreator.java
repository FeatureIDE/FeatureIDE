package com.sleepycat.bind.tuple;
import de.ovgu.cide.jakutil.*;
/** 
 * A concrete key creator that works in conjunction with a {@link TupleTupleMarshalledBinding}. This key creator works by calling the methods
 * of the {@link MarshalledTupleKeyEntity} interface to create and clear the
 * index key.
 * <p>
 * Note that a marshalled tuple key creator is somewhat less efficient than a
 * non-marshalled key tuple creator because more conversions are needed. A
 * marshalled key creator must convert the entry to an object in order to create
 * the key, while an unmarshalled key creator does not.
 * </p>
 * @author Mark Hayes
 */
public class TupleTupleMarshalledKeyCreator extends TupleTupleKeyCreator {
  private String keyName;
  private TupleTupleMarshalledBinding binding;
  /** 
 * Creates a tuple-tuple marshalled key creator.
 * @param bindingis the binding used for the tuple-tuple entity.
 * @param keyNameis the key name passed to the {@link MarshalledTupleKeyEntity#marshalSecondaryKey} method to
 * identify the index key.
 */
  public TupleTupleMarshalledKeyCreator(  TupleTupleMarshalledBinding binding,  String keyName){
    this.binding=binding;
    this.keyName=keyName;
  }
  public boolean createSecondaryKey(  TupleInput primaryKeyInput,  TupleInput dataInput,  TupleOutput indexKeyOutput){
    MarshalledTupleKeyEntity entity=(MarshalledTupleKeyEntity)binding.entryToObject(primaryKeyInput,dataInput);
    return entity.marshalSecondaryKey(keyName,indexKeyOutput);
  }
  public boolean nullifyForeignKey(  TupleInput dataInput,  TupleOutput dataOutput){
    MarshalledTupleKeyEntity entity=(MarshalledTupleKeyEntity)binding.entryToObject(null,dataInput);
    if (entity.nullifyForeignKey(keyName)) {
      binding.objectToData(entity,dataOutput);
      return true;
    }
 else {
      return false;
    }
  }
}
