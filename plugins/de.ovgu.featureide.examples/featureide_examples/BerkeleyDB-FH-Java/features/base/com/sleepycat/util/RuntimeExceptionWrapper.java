package com.sleepycat.util;
import de.ovgu.cide.jakutil.*;
/** 
 * A RuntimeException that can contain nested exceptions.
 * @author Mark Hayes
 */
public class RuntimeExceptionWrapper extends RuntimeException implements ExceptionWrapper {
  private Throwable e;
  public RuntimeExceptionWrapper(  Throwable e){
    super(e.getMessage());
    this.e=e;
  }
  /** 
 * @deprecated replaced by {@link #getCause}.
 */
  public Throwable getDetail(){
    return e;
  }
  public Throwable getCause(){
    return e;
  }
}
