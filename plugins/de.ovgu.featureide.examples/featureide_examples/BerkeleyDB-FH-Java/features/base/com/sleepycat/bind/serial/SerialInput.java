package com.sleepycat.bind.serial;
import java.io.IOException;
import java.io.InputStream;
import java.io.ObjectInputStream;
import java.io.ObjectStreamClass;
import com.sleepycat.je.DatabaseException;
import com.sleepycat.util.RuntimeExceptionWrapper;
import de.ovgu.cide.jakutil.*;
/** 
 * A specialized <code>ObjectInputStream</code> that gets class description
 * information from a <code>ClassCatalog</code>. It is used by
 * <code>SerialBinding</code>.
 * <p>
 * This class is used instead of an {@link ObjectInputStream}, which it
 * extends, to read an object stream written by the {@link SerialOutput} class.
 * For reading objects from a database normally one of the serial binding
 * classes is used. {@link SerialInput} is used when an {@link ObjectInputStream} is needed along with compact storage. A {@link ClassCatalog} must be supplied, however, to stored shared class descriptions.
 * </p>
 * @author Mark Hayes
 */
public class SerialInput extends ObjectInputStream {
  private ClassCatalog classCatalog;
  private ClassLoader classLoader;
  /** 
 * Creates a serial input stream.
 * @param inis the input stream from which compact serialized objects will
 * be read.
 * @param classCatalogis the catalog containing the class descriptions for the
 * serialized objects.
 */
  public SerialInput(  InputStream in,  ClassCatalog classCatalog) throws IOException {
    this(in,classCatalog,null);
  }
  /** 
 * Creates a serial input stream.
 * @param inis the input stream from which compact serialized objects will
 * be read.
 * @param classCatalogis the catalog containing the class descriptions for the
 * serialized objects.
 * @param classLoaderis the class loader to use, or null if a default class loader
 * should be used.
 */
  public SerialInput(  InputStream in,  ClassCatalog classCatalog,  ClassLoader classLoader) throws IOException {
    super(in);
    this.classCatalog=classCatalog;
    this.classLoader=classLoader;
  }
  protected ObjectStreamClass readClassDescriptor() throws IOException, ClassNotFoundException {
    try {
      byte len=readByte();
      byte[] id=new byte[len];
      readFully(id);
      return classCatalog.getClassFormat(id);
    }
 catch (    DatabaseException e) {
      throw new RuntimeExceptionWrapper(e);
    }
  }
  protected Class resolveClass(  ObjectStreamClass desc) throws IOException, ClassNotFoundException {
    if (classLoader != null) {
      try {
        return Class.forName(desc.getName(),false,classLoader);
      }
 catch (      ClassNotFoundException e) {
        return super.resolveClass(desc);
      }
    }
 else {
      return super.resolveClass(desc);
    }
  }
}
