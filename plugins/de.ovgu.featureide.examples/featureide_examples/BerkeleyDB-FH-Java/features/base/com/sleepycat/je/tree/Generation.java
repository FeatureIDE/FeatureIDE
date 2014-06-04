package com.sleepycat.je.tree;
import de.ovgu.cide.jakutil.*;
public final class Generation {
  static private long nextGeneration=0;
  static long getNextGeneration(){
    return nextGeneration++;
  }
}
