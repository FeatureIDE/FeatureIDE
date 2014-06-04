

import java.io.*;

public class PlaygroundIO {
  private static final String FILE_HEADER="Game_of_Life.Playground";
  private static final String WIDTH_TOKEN="width ";
  private static final String HEIGHT_TOKEN="height ";
  private static final String DATA_BEGIN_TOKEN="Begin";
  private static final String DATA_END_TOKEN="End";
  private static boolean isSquare(  int[][] pg){
    if (pg.length == 0)     return true;
    int width=pg[0].length;
    for (int r=1; r < pg.length; r++) {
      if (pg[r].length != width)       return false;
    }
    return true;
  }
  public static void saveToFile(  int[][] pg,  File dest) throws IOException {
    FileWriter playgroundWriter=null;
    if (dest == null) {
      throw new IllegalArgumentException("dest was null");
    }
 else     if (pg == null) {
      throw new IllegalArgumentException("pg was null");
    }
    if (!isSquare(pg)) {
      throw new IllegalArgumentException("tried to save a non-square playground");
    }
    if (dest.exists()) {
      dest.delete();
    }
    if (!dest.createNewFile()) {
      throw new IOException("File Could Not Be Created" + dest.getName());
    }
    if (!dest.canWrite()) {
      throw new IOException("cannot write to" + dest.getName());
    }
    try {
      int height=pg.length;
      int width=pg[0].length;
      playgroundWriter=new FileWriter(dest);
      playgroundWriter.write(FILE_HEADER + "\n");
      playgroundWriter.write(HEIGHT_TOKEN + height + "\n");
      playgroundWriter.write(WIDTH_TOKEN + width + "\n");
      playgroundWriter.write(DATA_BEGIN_TOKEN + "\n");
      for (int r=0; r < height; r++) {
        for (int i=0; i < width; i++) {
          playgroundWriter.write(String.valueOf(pg[r][i]));
        }
        playgroundWriter.write("\n");
      }
      playgroundWriter.write(DATA_END_TOKEN);
    }
 catch (    final IOException e) {
      throw new IOException("Unexpected Write Exception Occured");
    }
 finally {
      if (playgroundWriter != null) {
        playgroundWriter.close();
      }
    }
  }
  public static int[][] loadFromFile(  File source) throws IOException {
    if (!source.exists()) {
      throw new IOException("Given File Doesnt Exist" + source.getName());
    }
 else     if (!source.canRead()) {
      throw new IOException("Given File Is Not Readable" + source.getName());
    }
    BufferedReader reader=new BufferedReader(new FileReader(source));
    if (!reader.ready()) {
      throw new IOException("Given File Is Empty" + source.getName());
    }
    int[][] playground;
    String line;
    if (!reader.readLine().equals(FILE_HEADER)) {
      throw new IOException("Illegal format");
    }
    try {
      int width;
      int height;
      line=reader.readLine();
      if (!line.startsWith(HEIGHT_TOKEN)) {
        throw new IOException("Illegal format");
      }
 else {
        height=Integer.parseInt(line.substring(HEIGHT_TOKEN.length()));
      }
      line=reader.readLine();
      if (!line.startsWith(WIDTH_TOKEN)) {
        throw new IOException("Illegal format");
      }
 else {
        width=Integer.parseInt(line.substring(WIDTH_TOKEN.length()));
      }
      if (!reader.readLine().equals(DATA_BEGIN_TOKEN)) {
        throw new IOException("Illegal format");
      }
      playground=new int[width][height];
      for (int r=0; r < height; r++) {
        line=reader.readLine();
        for (int i=0; i < width; i++) {
          playground[r][i]=Integer.parseInt(line.substring(i,i + 1));
        }
      }
      if (!reader.readLine().equals(DATA_END_TOKEN)) {
        throw new IOException("Illegal format");
      }
    }
 catch (    NumberFormatException e) {
      throw new IOException("Illegal format");
    }
    return playground;
  }
}
