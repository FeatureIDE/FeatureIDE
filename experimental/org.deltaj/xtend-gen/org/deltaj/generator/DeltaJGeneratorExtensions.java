package org.deltaj.generator;

import com.google.common.base.Objects;
import com.google.inject.Inject;
import java.util.List;
import org.deltaj.deltaj.JavaVerbatim;
import org.deltaj.deltaj.Product;
import org.deltaj.deltaj.ProductLine;
import org.deltaj.generator.DeltaJClassBuilder;
import org.deltaj.util.ClassCollection;
import org.eclipse.xtend2.lib.StringConcatenation;
import org.eclipse.xtext.util.Strings;
import org.eclipse.xtext.xbase.lib.StringExtensions;

@SuppressWarnings("all")
public class DeltaJGeneratorExtensions {
  @Inject
  private DeltaJClassBuilder classBuilder;
  
  public String fileName(final Product product, final org.deltaj.deltaj.Class clazz) {
    String _packageName = this.packageName(product);
    String _folderName = this.folderName(_packageName);
    String _plus = (_folderName + "/");
    String _name = clazz.getName();
    String _plus_1 = (_plus + _name);
    return (_plus_1 + ".java");
  }
  
  public String packageName(final Product product) {
    ProductLine _productLine = product.getProductLine();
    String _name = _productLine.getName();
    String _nameToPackage = this.nameToPackage(_name);
    String _name_1 = product.getName();
    String _nameToPackage_1 = this.nameToPackage(_name_1);
    return this.concatPackage(_nameToPackage, _nameToPackage_1);
  }
  
  public String qualifiedName(final Product product, final org.deltaj.deltaj.Class clazz) {
    String _packageName = this.packageName(product);
    String _name = clazz.getName();
    return this.concatPackage(_packageName, _name);
  }
  
  public String nameToPackage(final String name) {
    return name.toLowerCase();
  }
  
  public String concatPackage(final String prefix, final String suffix) {
    String _xifexpression = null;
    boolean _isNullOrEmpty = StringExtensions.isNullOrEmpty(prefix);
    if (_isNullOrEmpty) {
      _xifexpression = suffix;
    } else {
      _xifexpression = ((prefix + ".") + suffix);
    }
    return _xifexpression;
  }
  
  public String folderName(final String javaPackageName) {
    String _xifexpression = null;
    boolean _notEquals = (!Objects.equal(javaPackageName, null));
    if (_notEquals) {
      _xifexpression = javaPackageName.replace(".", "/");
    } else {
      _xifexpression = "";
    }
    return _xifexpression;
  }
  
  public DeltaJClassBuilder classBuilder() {
    return this.classBuilder;
  }
  
  public ClassCollection classesToGenerate(final Product product) {
    return this.classBuilder.classesToGenerate(product);
  }
  
  public String extractJavaVerbatimCode(final JavaVerbatim javaVerbatim) {
    String _verbatim = javaVerbatim.getVerbatim();
    String _replace = _verbatim.replace("**Java:", "");
    return _replace.replace(":Java**", "");
  }
  
  public List<String> javaVerbatimLines(final JavaVerbatim javaVerbatim) {
    String _verbatim = javaVerbatim.getVerbatim();
    String _property = System.getProperty("line.separator");
    return Strings.split(_verbatim, _property);
  }
  
  public StringConcatenation addNewLineIfNotEmpty(final StringConcatenation buffer) {
    StringConcatenation _xblockexpression = null;
    {
      int _length = buffer.length();
      boolean _greaterThan = (_length > 0);
      if (_greaterThan) {
        buffer.newLine();
      }
      _xblockexpression = buffer;
    }
    return _xblockexpression;
  }
}
