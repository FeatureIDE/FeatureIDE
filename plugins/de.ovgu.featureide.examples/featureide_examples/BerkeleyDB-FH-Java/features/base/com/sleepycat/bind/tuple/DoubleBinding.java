package com.sleepycat.bind.tuple;
import com.sleepycat.je.DatabaseEntry;
import de.ovgu.cide.jakutil.*;
/** 
 * A concrete <code>TupleBinding</code> for a <code>Double</code> primitive
 * wrapper or a <code>double</code> primitive.
 * <p>
 * There are two ways to use this class:
 * </p>
 * <ol>
 * <li>When using the {@link com.sleepycat.je} package directly, the static
 * methods in this class can be used to convert between primitive values and{@link DatabaseEntry} objects.</li>
 * <li>When using the {@link com.sleepycat.collections} package, an instance of
 * this class can be used with any stored collection. The easiest way to obtain
 * a binding instance is with the {@link TupleBinding#getPrimitiveBinding}method.</li>
 * </ol>
 */
public class DoubleBinding extends TupleBinding {
  private static final int DOUBLE_SIZE=8;
  public Object entryToObject(  TupleInput input){
    return new Double(input.readDouble());
  }
  public void objectToEntry(  Object object,  TupleOutput output){
    output.writeDouble(((Number)object).doubleValue());
  }
  protected TupleOutput getTupleOutput(  Object object){
    return sizedOutput();
  }
  /** 
 * Converts an entry buffer into a simple <code>double</code> value.
 * @param entryis the source entry buffer.
 * @return the resulting value.
 */
  public static double entryToDouble(  DatabaseEntry entry){
    return entryToInput(entry).readDouble();
  }
  /** 
 * Converts a simple <code>double</code> value into an entry buffer.
 * @param valis the source value.
 * @param entryis the destination entry buffer.
 */
  public static void doubleToEntry(  double val,  DatabaseEntry entry){
    outputToEntry(sizedOutput().writeDouble(val),entry);
  }
  /** 
 * Returns a tuple output object of the exact size needed, to avoid wasting
 * space when a single primitive is output.
 */
  private static TupleOutput sizedOutput(){
    return new TupleOutput(new byte[DOUBLE_SIZE]);
  }
}
