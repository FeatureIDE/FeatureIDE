package com.sleepycat.util;
import java.io.IOException;
import de.ovgu.cide.jakutil.*;
/** 
 * An IOException that can contain nested exceptions.
 * @author Mark Hayes
 */
public class IOExceptionWrapper extends IOException implements ExceptionWrapper {
  private Throwable e;
  public IOExceptionWrapper(  Throwable e){
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
