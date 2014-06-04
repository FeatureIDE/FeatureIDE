package com.sleepycat.je.tree;
import de.ovgu.cide.jakutil.*;
/** 
 * Error to indicate that a bottom level BIN has cursors on it during a
 * delete subtree operation.
 */
public class CursorsExistException extends Exception {
  public static final CursorsExistException CURSORS_EXIST=new CursorsExistException();
  private CursorsExistException(){
  }
}
