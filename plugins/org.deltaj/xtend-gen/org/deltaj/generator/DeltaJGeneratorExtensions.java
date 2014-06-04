package org.deltaj.generator;

import com.google.inject.Inject;
import java.util.List;
import org.deltaj.deltaj.JavaVerbatim;
import org.deltaj.deltaj.Product;
import org.deltaj.deltaj.ProductLine;
import org.deltaj.generator.DeltaJClassBuilder;
import org.deltaj.util.ClassCollection;
import org.eclipse.xtend2.lib.StringConcatenation;
import org.eclipse.xtext.util.Strings;
import org.eclipse.xtext.xbase.lib.IntegerExtensions;
import org.eclipse.xtext.xbase.lib.ObjectExtensions;
import org.eclipse.xtext.xbase.lib.StringExtensions;

@SuppressWarnings("all")
public class DeltaJGeneratorExtensions {
  @Inject
  private DeltaJClassBuilder classBuilder;
  
  public String fileName(final Product product, final org.deltaj.deltaj.Class clazz) {
    String _packageName = this.packageName(product);
    String _folderName = this.folderName(_packageName);
    String _operator_plus = StringExtensions.operator_plus(_folderName, "/");
    String _name = clazz.getName();
    String _operator_plus_1 = StringExtensions.operator_plus(_operator_plus, _name);
    String _operator_plus_2 = StringExtensions.operator_plus(_operator_plus_1, ".java");
    return _operator_plus_2;
  }
  
  public String packageName(final Product product) {
    ProductLine _productLine = product.getProductLine();
    String _name = _productLine.getName();
    String _nameToPackage = this.nameToPackage(_name);
    String _name_1 = product.getName();
    String _nameToPackage_1 = this.nameToPackage(_name_1);
    String _concatPackage = this.concatPackage(_nameToPackage, _nameToPackage_1);
    return _concatPackage;
  }
  
  public String qualifiedName(final Product product, final org.deltaj.deltaj.Class clazz) {
    String _packageName = this.packageName(product);
    String _name = clazz.getName();
    String _concatPackage = this.concatPackage(_packageName, _name);
    return _concatPackage;
  }
  
  public String nameToPackage(final String name) {
    String _lowerCase = name.toLowerCase();
    return _lowerCase;
  }
  
  public String concatPackage(final String prefix, final String suffix) {
    String _xifexpression = null;
    boolean _isNullOrEmpty = StringExtensions.isNullOrEmpty(prefix);
    if (_isNullOrEmpty) {
      _xifexpression = suffix;
    } else {
      String _operator_plus = StringExtensions.operator_plus(prefix, ".");
      String _operator_plus_1 = StringExtensions.operator_plus(_operator_plus, suffix);
      _xifexpression = _operator_plus_1;
    }
    return _xifexpression;
  }
  
  public String folderName(final String javaPackageName) {
    String _xifexpression = null;
    boolean _operator_notEquals = ObjectExtensions.operator_notEquals(javaPackageName, null);
    if (_operator_notEquals) {
      String _replace = javaPackageName.replace(".", "/");
      _xifexpression = _replace;
    } else {
      _xifexpression = "";
    }
    return _xifexpression;
  }
  
  public DeltaJClassBuilder classBuilder() {
    return this.classBuilder;
  }
  
  public ClassCollection classesToGenerate(final Product product) {
    ClassCollection _classesToGenerate = this.classBuilder.classesToGenerate(product);
    return _classesToGenerate;
  }
  
  public String extractJavaVerbatimCode(final JavaVerbatim javaVerbatim) {
    String _verbatim = javaVerbatim.getVerbatim();
    String _replace = _verbatim.replace("**Java:", "");
    String _replace_1 = _replace.replace(":Java**", "");
    return _replace_1;
  }
  
  public List<String> javaVerbatimLines(final JavaVerbatim javaVerbatim) {
    String _verbatim = javaVerbatim.getVerbatim();
    String _property = System.getProperty("line.separator");
    List<String> _split = Strings.split(_verbatim, _property);
    return _split;
  }
  
  public StringConcatenation addNewLineIfNotEmpty(final StringConcatenation buffer) {
    StringConcatenation _xblockexpression = null;
    {
      int _length = buffer.length();
      boolean _operator_greaterThan = IntegerExtensions.operator_greaterThan(_length, 0);
      if (_operator_greaterThan) {
        buffer.newLine();
      }
      _xblockexpression = (buffer);
    }
    return _xblockexpression;
  }
}
