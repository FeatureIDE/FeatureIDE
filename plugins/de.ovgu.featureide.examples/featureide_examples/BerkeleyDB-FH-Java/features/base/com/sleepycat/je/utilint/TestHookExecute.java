package com.sleepycat.je.utilint;
import de.ovgu.cide.jakutil.*;
/** 
 */
public class TestHookExecute {
  public static boolean doHookIfSet(  TestHook testHook){
    if (testHook != null) {
      testHook.doHook();
    }
    return true;
  }
}
