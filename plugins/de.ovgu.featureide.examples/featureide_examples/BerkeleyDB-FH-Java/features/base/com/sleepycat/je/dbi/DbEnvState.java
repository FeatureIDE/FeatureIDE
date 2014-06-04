package com.sleepycat.je.dbi;
import com.sleepycat.je.DatabaseException;
import de.ovgu.cide.jakutil.*;
/** 
 * DbEnvState implements a typesafe enumeration of environment states
 * and does state change validation.
 */
class DbEnvState {
  private static final boolean DEBUG=false;
  private String name;
  public static final DbEnvState INIT=new DbEnvState("initialized");
  public static final DbEnvState OPEN=new DbEnvState("open");
  public static final DbEnvState CLOSED=new DbEnvState("closed");
  public static final DbEnvState INVALID=new DbEnvState("invalid");
  public static final DbEnvState[] VALID_FOR_OPEN={INIT,CLOSED};
  public static final DbEnvState[] VALID_FOR_CLOSE={INIT,OPEN,INVALID};
  public static final DbEnvState[] VALID_FOR_REMOVE={INIT,CLOSED};
  DbEnvState(  String name){
    this.name=name;
  }
  public String toString(){
    return name;
  }
  void checkState(  DbEnvState[] validPrevStates,  DbEnvState newState) throws DatabaseException {
    if (DEBUG) {
      System.out.println("newState = " + newState + " currentState = "+ name);
    }
    boolean transitionOk=false;
    for (int i=0; i < validPrevStates.length; i++) {
      if (this == validPrevStates[i]) {
        transitionOk=true;
        break;
      }
    }
    if (!transitionOk) {
      throw new DatabaseException("Can't go from environment state " + toString() + " to "+ newState.toString());
    }
  }
}
