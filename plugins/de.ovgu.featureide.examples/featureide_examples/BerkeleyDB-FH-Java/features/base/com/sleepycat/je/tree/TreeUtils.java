package com.sleepycat.je.tree;
import de.ovgu.cide.jakutil.*;
/** 
 * Miscellaneous Tree utilities.
 */
public class TreeUtils {
  static private final String SPACES="                                " + "                                " + "                                "+ "                                ";
  /** 
 * For tree dumper.
 */
  public static String indent(  int nSpaces){
    return SPACES.substring(0,nSpaces);
  }
  public static String dumpByteArray(  byte[] b){
    StringBuffer sb=new StringBuffer();
    if (b != null) {
      if (Key.DUMP_BINARY) {
        for (int i=0; i < b.length; i++) {
          sb.append(b[i] & 0xFF);
          sb.append(" ");
        }
      }
 else {
        sb.append(new String(b));
      }
    }
 else {
      sb.append("null");
    }
    return sb.toString();
  }
}
