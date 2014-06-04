package com.sleepycat.je.log;
import java.io.File;
import java.io.FilenameFilter;
import java.util.StringTokenizer;
import de.ovgu.cide.jakutil.*;
/** 
 * JEFileFilters are used for listing je files. 
 */
class JEFileFilter implements FilenameFilter {
  String[] suffix;
  JEFileFilter(  String[] suffix){
    this.suffix=suffix;
  }
  private boolean matches(  String fileSuffix){
    for (int i=0; i < suffix.length; i++) {
      if (fileSuffix.equalsIgnoreCase(suffix[i])) {
        return true;
      }
    }
    return false;
  }
  /** 
 * A JE file has to be of the format nnnnnnnn.suffix.
 */
  public boolean accept(  File dir,  String name){
    boolean ok=false;
    StringTokenizer tokenizer=new StringTokenizer(name,".");
    int nTokens=tokenizer.countTokens();
    if (nTokens == 2 || nTokens == 3) {
      boolean hasVersion=(nTokens == 3);
      String fileNumber=tokenizer.nextToken();
      String fileSuffix="." + tokenizer.nextToken();
      String fileVersion=(hasVersion ? tokenizer.nextToken() : null);
      if ((fileNumber.length() == 8) && matches(fileSuffix)) {
        try {
          Integer.parseInt(fileNumber,16);
          ok=true;
        }
 catch (        NumberFormatException e) {
          ok=false;
        }
        if (hasVersion) {
          try {
            Integer.parseInt(fileVersion);
            ok=true;
          }
 catch (          NumberFormatException e) {
            ok=false;
          }
        }
      }
    }
    return ok;
  }
}
