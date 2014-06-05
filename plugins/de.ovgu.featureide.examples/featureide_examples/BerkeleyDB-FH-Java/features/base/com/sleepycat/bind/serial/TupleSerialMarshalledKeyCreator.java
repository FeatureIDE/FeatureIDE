package com.sleepycat.bind.serial;
import com.sleepycat.bind.tuple.MarshalledTupleKeyEntity;
import com.sleepycat.bind.tuple.TupleInput;
import com.sleepycat.bind.tuple.TupleOutput;
import de.ovgu.cide.jakutil.*;
/** 
 * A concrete key creator that works in conjunction with a {@link TupleSerialMarshalledBinding}. This key creator works by calling the methods
 * of the {@link MarshalledTupleKeyEntity} interface to create and clear the
 * index key fields.
 * @author Mark Hayes
 */
public class TupleSerialMarshalledKeyCreator extends TupleSerialKeyCreator {
  private TupleSerialMarshalledBinding binding;
  private String keyName;
  /** 
 * Creates a tuple-serial marshalled key creator.
 * @param bindingis the binding used for the tuple-serial entity.
 * @param keyNameis the key name passed to the {@link MarshalledTupleKeyEntity#marshalSecondaryKey} method to
 * identify the index key.
 */
  public TupleSerialMarshalledKeyCreator(  TupleSerialMarshalledBinding binding,  String keyName){
    super(binding.dataBinding);
    this.binding=binding;
    this.keyName=keyName;
    if (dataBinding == null) {
      throw new NullPointerException("dataBinding may not be null");
    }
  }
  public boolean createSecondaryKey(  TupleInput primaryKeyInput,  Object dataInput,  TupleOutput indexKeyOutput){
    MarshalledTupleKeyEntity entity=(MarshalledTupleKeyEntity)binding.entryToObject(primaryKeyInput,dataInput);
    return entity.marshalSecondaryKey(keyName,indexKeyOutput);
  }
  public Object nullifyForeignKey(  Object dataInput){
    MarshalledTupleKeyEntity entity=(MarshalledTupleKeyEntity)binding.entryToObject(null,dataInput);
    return entity.nullifyForeignKey(keyName) ? dataInput : null;
  }
}
