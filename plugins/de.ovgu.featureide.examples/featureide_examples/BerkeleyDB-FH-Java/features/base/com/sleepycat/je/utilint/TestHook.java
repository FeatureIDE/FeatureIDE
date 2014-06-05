package com.sleepycat.je.utilint;
import java.io.IOException;
import de.ovgu.cide.jakutil.*;
/** 
 * TestHook is used induce testing behavior that can't be provoked externally.
 * For example, unit tests may use hooks to throw IOExceptions, or to cause
 * waiting behavior.
 * To use this, a unit test should extend TestHook with a class that overrides
 * the desired method. The desired code will have a method that allows the unit
 * test to specify a hook, and will execute the hook if it is non-null.
 */
public interface TestHook {
  public void doIOHook() throws IOException ;
  public void doHook();
  public Object getHookValue();
}
