package org.deltaj.generator;

import java.util.Arrays;
import org.deltaj.deltaj.BasicType;
import org.deltaj.deltaj.ClassType;
import org.deltaj.deltaj.Type;
import org.deltaj.deltaj.TypeVariable;
import org.eclipse.xtend2.lib.StringConcatenation;

@SuppressWarnings("all")
public class DeltaJTypeGenerator {
  protected CharSequence _compileType(final Type type) {
    StringConcatenation _builder = new StringConcatenation();
    return _builder;
  }
  
  protected CharSequence _compileType(final TypeVariable type) {
    StringConcatenation _builder = new StringConcatenation();
    String _varName = type.getVarName();
    _builder.append(_varName, "");
    return _builder;
  }
  
  protected CharSequence _compileType(final ClassType type) {
    StringConcatenation _builder = new StringConcatenation();
    String _classref = type.getClassref();
    _builder.append(_classref, "");
    return _builder;
  }
  
  protected CharSequence _compileType(final BasicType type) {
    StringConcatenation _builder = new StringConcatenation();
    String _basic = type.getBasic();
    _builder.append(_basic, "");
    return _builder;
  }
  
  public CharSequence compileType(final Type type) {
    if (type instanceof BasicType) {
      return _compileType((BasicType)type);
    } else if (type instanceof ClassType) {
      return _compileType((ClassType)type);
    } else if (type instanceof TypeVariable) {
      return _compileType((TypeVariable)type);
    } else if (type != null) {
      return _compileType(type);
    } else {
      throw new IllegalArgumentException("Unhandled parameter types: " +
        Arrays.<Object>asList(type).toString());
    }
  }
}
