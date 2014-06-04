package com.sleepycat.je;
import com.sleepycat.je.dbi.EnvironmentImpl;
import de.ovgu.cide.jakutil.*;
/** 
 * Javadoc for this public class is generated
 * via the doc templates in the doc_src directory.
 */
public class RunRecoveryException extends DatabaseException {
  private boolean alreadyThrown=false;
  public RunRecoveryException(  EnvironmentImpl env){
    super();
    invalidate(env);
  }
  public RunRecoveryException(  EnvironmentImpl env,  Throwable t){
    super(t);
    invalidate(env);
  }
  public RunRecoveryException(  EnvironmentImpl env,  String message){
    super(message);
    invalidate(env);
  }
  public RunRecoveryException(  EnvironmentImpl env,  String message,  Throwable t){
    super(message,t);
    invalidate(env);
  }
  private void invalidate(  EnvironmentImpl env){
    if (env != null) {
      env.invalidate(this);
    }
  }
  public void setAlreadyThrown(){
    alreadyThrown=true;
  }
  public String toString(){
    if (alreadyThrown) {
      return "Environment invalid because of previous exception: " + super.toString();
    }
 else {
      return super.toString();
    }
  }
}
