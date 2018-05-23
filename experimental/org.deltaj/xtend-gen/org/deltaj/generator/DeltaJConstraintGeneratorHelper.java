package org.deltaj.generator;

import com.google.inject.Inject;
import java.util.Arrays;
import java.util.List;
import org.deltaj.deltaj.Cast;
import org.deltaj.deltaj.Expression;
import org.deltaj.deltaj.JavaVerbatim;
import org.deltaj.deltaj.New;
import org.deltaj.deltaj.Statement;
import org.deltaj.deltaj.Type;
import org.deltaj.generator.DeltaJGeneratorExtensions;
import org.deltaj.generator.DeltaJTypeGenerator;
import org.deltaj.util.DeltaJNodeModelUtils;
import org.eclipse.xtend2.lib.StringConcatenation;
import org.eclipse.xtext.xbase.lib.Extension;
import org.eclipse.xtext.xbase.lib.Functions.Function1;
import org.eclipse.xtext.xbase.lib.IterableExtensions;
import org.eclipse.xtext.xbase.lib.ListExtensions;

@SuppressWarnings("all")
public class DeltaJConstraintGeneratorHelper {
  @Inject
  private DeltaJNodeModelUtils nodeModelUtils;
  
  @Inject
  @Extension
  private DeltaJTypeGenerator typeGenerator;
  
  @Inject
  @Extension
  private DeltaJGeneratorExtensions _deltaJGeneratorExtensions;
  
  protected CharSequence _genComment(final Statement statement) {
    StringConcatenation _builder = new StringConcatenation();
    _builder.append("/* ");
    String _programText = this.nodeModelUtils.getProgramText(statement);
    _builder.append(_programText, "");
    _builder.append(" */");
    return _builder;
  }
  
  protected CharSequence _genComment(final JavaVerbatim javaVerbatim) {
    List<String> _javaVerbatimLines = this._deltaJGeneratorExtensions.javaVerbatimLines(javaVerbatim);
    final Function1<String, String> _function = new Function1<String, String>() {
      @Override
      public String apply(final String line) {
        return ("// " + line);
      }
    };
    List<String> _map = ListExtensions.<String, String>map(_javaVerbatimLines, _function);
    return IterableExtensions.join(_map, "\n");
  }
  
  public CharSequence genComment(final Expression exp) {
    StringConcatenation _builder = new StringConcatenation();
    _builder.append("// ");
    String _programText = this.nodeModelUtils.getProgramText(exp);
    _builder.append(_programText, "");
    return _builder;
  }
  
  public CharSequence genClassConstraint(final String class_, final New new_) {
    StringConcatenation _builder = new StringConcatenation();
    _builder.append("class(");
    _builder.append(class_, "");
    _builder.append(") ");
    CharSequence _genComment = this.genComment(new_);
    _builder.append(_genComment, "");
    return _builder;
  }
  
  public CharSequence genSubtypeConstraint(final Type candidate, final Type expectedType, final Expression exp) {
    StringConcatenation _builder = new StringConcatenation();
    _builder.append("subtype(");
    CharSequence _compileType = this.typeGenerator.compileType(candidate);
    _builder.append(_compileType, "");
    _builder.append(", ");
    CharSequence _compileType_1 = this.typeGenerator.compileType(expectedType);
    _builder.append(_compileType_1, "");
    _builder.append(") ");
    CharSequence _genComment = this.genComment(exp);
    _builder.append(_genComment, "");
    return _builder;
  }
  
  public CharSequence genPlusConstraint(final Type left, final Type right, final Type plusType, final Expression exp) {
    StringConcatenation _builder = new StringConcatenation();
    _builder.append("plus(");
    CharSequence _compileType = this.typeGenerator.compileType(left);
    _builder.append(_compileType, "");
    _builder.append(", ");
    CharSequence _compileType_1 = this.typeGenerator.compileType(right);
    _builder.append(_compileType_1, "");
    _builder.append(", ");
    CharSequence _compileType_2 = this.typeGenerator.compileType(plusType);
    _builder.append(_compileType_2, "");
    _builder.append(") ");
    CharSequence _genComment = this.genComment(exp);
    _builder.append(_genComment, "");
    return _builder;
  }
  
  public CharSequence genCastConstraint(final String castTo, final Type candidate, final Cast cast) {
    StringConcatenation _builder = new StringConcatenation();
    _builder.append("cast(");
    _builder.append(castTo, "");
    _builder.append(", ");
    CharSequence _compileType = this.typeGenerator.compileType(candidate);
    _builder.append(_compileType, "");
    _builder.append(") ");
    CharSequence _genComment = this.genComment(cast);
    _builder.append(_genComment, "");
    return _builder;
  }
  
  public CharSequence genFieldConstraint(final Type containingType, final String fieldName, final Type fieldType, final Expression exp) {
    StringConcatenation _builder = new StringConcatenation();
    _builder.append("field(");
    CharSequence _compileType = this.typeGenerator.compileType(containingType);
    _builder.append(_compileType, "");
    _builder.append(", ");
    _builder.append(fieldName, "");
    _builder.append(", ");
    CharSequence _compileType_1 = this.typeGenerator.compileType(fieldType);
    _builder.append(_compileType_1, "");
    _builder.append(") ");
    CharSequence _genComment = this.genComment(exp);
    _builder.append(_genComment, "");
    return _builder;
  }
  
  public CharSequence genMethodConstraint(final Type receiverType, final String methodName, final Type returnType, final List<Type> typesForParams, final Expression exp) {
    StringConcatenation _builder = new StringConcatenation();
    _builder.append("method(");
    CharSequence _compileType = this.typeGenerator.compileType(receiverType);
    _builder.append(_compileType, "");
    _builder.append(", ");
    _builder.append(methodName, "");
    _builder.append(", (");
    final Function1<Type, CharSequence> _function = new Function1<Type, CharSequence>() {
      @Override
      public CharSequence apply(final Type t) {
        return DeltaJConstraintGeneratorHelper.this.typeGenerator.compileType(t);
      }
    };
    List<CharSequence> _map = ListExtensions.<Type, CharSequence>map(typesForParams, _function);
    String _join = IterableExtensions.join(_map, ", ");
    _builder.append(_join, "");
    _builder.append(") -> ");
    CharSequence _compileType_1 = this.typeGenerator.compileType(returnType);
    _builder.append(_compileType_1, "");
    _builder.append(") ");
    CharSequence _genComment = this.genComment(exp);
    _builder.append(_genComment, "");
    return _builder;
  }
  
  public CharSequence genComment(final Statement javaVerbatim) {
    if (javaVerbatim instanceof JavaVerbatim) {
      return _genComment((JavaVerbatim)javaVerbatim);
    } else if (javaVerbatim != null) {
      return _genComment(javaVerbatim);
    } else {
      throw new IllegalArgumentException("Unhandled parameter types: " +
        Arrays.<Object>asList(javaVerbatim).toString());
    }
  }
}
