package org.deltaj.generator;

import com.google.inject.Inject;
import java.util.Arrays;
import java.util.LinkedList;
import org.deltaj.deltaj.AndOrExpression;
import org.deltaj.deltaj.ArithmeticSigned;
import org.deltaj.deltaj.BooleanNegation;
import org.deltaj.deltaj.BooleanType;
import org.deltaj.deltaj.Cast;
import org.deltaj.deltaj.Comparison;
import org.deltaj.deltaj.Expression;
import org.deltaj.deltaj.Field;
import org.deltaj.deltaj.FieldSelection;
import org.deltaj.deltaj.IntType;
import org.deltaj.deltaj.Message;
import org.deltaj.deltaj.MethodCall;
import org.deltaj.deltaj.Minus;
import org.deltaj.deltaj.MultiOrDiv;
import org.deltaj.deltaj.New;
import org.deltaj.deltaj.Paren;
import org.deltaj.deltaj.Plus;
import org.deltaj.deltaj.Selection;
import org.deltaj.deltaj.Type;
import org.deltaj.deltaj.TypeForDeclaration;
import org.deltaj.deltaj.TypeVariable;
import org.deltaj.deltaj.TypedDeclaration;
import org.deltaj.deltaj.VariableAccess;
import org.deltaj.generator.DeltaJConstraintGeneratorHelper;
import org.deltaj.typing.DeltaJTypeSystem;
import org.deltaj.util.DeltaJTypeUtils;
import org.eclipse.emf.common.util.EList;
import org.eclipse.xtend2.lib.StringConcatenation;
import org.eclipse.xtext.xbase.lib.IntegerExtensions;

@SuppressWarnings("all")
public class DeltaJExpressionConstraintGenerator {
  private DeltaJTypeSystem typeSystem;
  
  private StringConcatenation buffer;
  
  @Inject
  private DeltaJConstraintGeneratorHelper constraintGeneratorHelper;
  
  public void init(final DeltaJTypeSystem ts, final StringConcatenation buf) {
      this.typeSystem = ts;
      this.buffer = buf;
  }
  
  public StringConcatenation genConstraints(final DeltaJTypeSystem ts, final Expression exp) {
    StringConcatenation _xblockexpression = null;
    {
      StringConcatenation _stringConcatenation = new StringConcatenation();
      this.init(ts, _stringConcatenation);
      this.genConstraintAndGetType(exp);
      _xblockexpression = (this.buffer);
    }
    return _xblockexpression;
  }
  
  public Type genConstraintAndGetType(final DeltaJTypeSystem ts, final StringConcatenation buffer, final Expression exp) {
    Type _xblockexpression = null;
    {
      this.init(ts, buffer);
      Type _genConstraintAndGetType = this.genConstraintAndGetType(exp);
      _xblockexpression = (_genConstraintAndGetType);
    }
    return _xblockexpression;
  }
  
  public Type genConstraintAndGetType(final Expression exp) {
    Type _genConstraintAndGetTypeCase = this.genConstraintAndGetTypeCase(exp);
    return _genConstraintAndGetTypeCase;
  }
  
  protected Type _genConstraintAndGetTypeCase(final Expression exp) {
    Type _methodBodyExpressionType = this.typeSystem.getMethodBodyExpressionType(exp);
    return _methodBodyExpressionType;
  }
  
  protected Type _genConstraintAndGetTypeCase(final Plus exp) {
    TypeVariable _xblockexpression = null;
    {
      Expression _left = exp.getLeft();
      Type _genConstraintAndGetType = this.genConstraintAndGetType(_left);
      Type leftType = _genConstraintAndGetType;
      this.buffer.newLineIfNotEmpty();
      Expression _right = exp.getRight();
      Type _genConstraintAndGetType_1 = this.genConstraintAndGetType(_right);
      Type rightType = _genConstraintAndGetType_1;
      this.buffer.newLineIfNotEmpty();
      TypeVariable _createTypeVariable = this.typeSystem.createTypeVariable();
      TypeVariable plusType = _createTypeVariable;
      CharSequence _genPlusConstraint = this.constraintGeneratorHelper.genPlusConstraint(leftType, rightType, plusType, exp);
      this.buffer.append(_genPlusConstraint);
      _xblockexpression = (plusType);
    }
    return _xblockexpression;
  }
  
  protected Type _genConstraintAndGetTypeCase(final Minus exp) {
    IntType _xblockexpression = null;
    {
      IntType _createIntType = DeltaJTypeUtils.createIntType();
      IntType intType = _createIntType;
      Expression _left = exp.getLeft();
      Expression _right = exp.getRight();
      this.genConstraintsForSubexpressions(exp, _left, _right, intType);
      _xblockexpression = (intType);
    }
    return _xblockexpression;
  }
  
  protected Type _genConstraintAndGetTypeCase(final MultiOrDiv exp) {
    IntType _xblockexpression = null;
    {
      IntType _createIntType = DeltaJTypeUtils.createIntType();
      IntType intType = _createIntType;
      Expression _left = exp.getLeft();
      Expression _right = exp.getRight();
      this.genConstraintsForSubexpressions(exp, _left, _right, intType);
      _xblockexpression = (intType);
    }
    return _xblockexpression;
  }
  
  protected Type _genConstraintAndGetTypeCase(final AndOrExpression exp) {
    BooleanType _xblockexpression = null;
    {
      BooleanType _createBooleanType = DeltaJTypeUtils.createBooleanType();
      BooleanType booleanType = _createBooleanType;
      Expression _left = exp.getLeft();
      Expression _right = exp.getRight();
      this.genConstraintsForSubexpressions(exp, _left, _right, booleanType);
      _xblockexpression = (booleanType);
    }
    return _xblockexpression;
  }
  
  protected Type _genConstraintAndGetTypeCase(final Comparison exp) {
    BooleanType _xblockexpression = null;
    {
      BooleanType _createBooleanType = DeltaJTypeUtils.createBooleanType();
      BooleanType booleanType = _createBooleanType;
      Expression _left = exp.getLeft();
      Expression _right = exp.getRight();
      IntType _createIntType = DeltaJTypeUtils.createIntType();
      this.genConstraintsForSubexpressions(exp, _left, _right, _createIntType);
      _xblockexpression = (booleanType);
    }
    return _xblockexpression;
  }
  
  public void genConstraintsForSubexpressions(final Expression main, final Expression left, final Expression right, final Type expectedType) {
      Type _genConstraintAndGetType = this.genConstraintAndGetType(left);
      Type leftType = _genConstraintAndGetType;
      this.buffer.newLineIfNotEmpty();
      CharSequence _genSubtypeConstraint = this.constraintGeneratorHelper.genSubtypeConstraint(leftType, expectedType, left);
      this.buffer.append(_genSubtypeConstraint);
      this.buffer.newLineIfNotEmpty();
      Type _genConstraintAndGetType_1 = this.genConstraintAndGetType(right);
      Type rightType = _genConstraintAndGetType_1;
      this.buffer.newLineIfNotEmpty();
      CharSequence _genSubtypeConstraint_1 = this.constraintGeneratorHelper.genSubtypeConstraint(rightType, expectedType, right);
      this.buffer.append(_genSubtypeConstraint_1);
      this.buffer.newLineIfNotEmpty();
      CharSequence _genComment = this.constraintGeneratorHelper.genComment(main);
      this.buffer.append(_genComment);
  }
  
  protected Type _genConstraintAndGetTypeCase(final ArithmeticSigned exp) {
    IntType _xblockexpression = null;
    {
      IntType _createIntType = DeltaJTypeUtils.createIntType();
      IntType intType = _createIntType;
      Expression _expression = exp.getExpression();
      this.genConstraintsForSubexpressions(exp, _expression, intType);
      _xblockexpression = (intType);
    }
    return _xblockexpression;
  }
  
  protected Type _genConstraintAndGetTypeCase(final BooleanNegation exp) {
    BooleanType _xblockexpression = null;
    {
      BooleanType _createBooleanType = DeltaJTypeUtils.createBooleanType();
      BooleanType booleanType = _createBooleanType;
      Expression _expression = exp.getExpression();
      this.genConstraintsForSubexpressions(exp, _expression, booleanType);
      _xblockexpression = (booleanType);
    }
    return _xblockexpression;
  }
  
  public void genConstraintsForSubexpressions(final Expression main, final Expression subExp, final Type expectedType) {
      Type _genConstraintAndGetType = this.genConstraintAndGetType(subExp);
      Type subExpType = _genConstraintAndGetType;
      this.buffer.newLineIfNotEmpty();
      CharSequence _genSubtypeConstraint = this.constraintGeneratorHelper.genSubtypeConstraint(subExpType, expectedType, subExp);
      this.buffer.append(_genSubtypeConstraint);
      this.buffer.newLineIfNotEmpty();
      CharSequence _genComment = this.constraintGeneratorHelper.genComment(main);
      this.buffer.append(_genComment);
  }
  
  protected Type _genConstraintAndGetTypeCase(final New exp) {
    Type _xblockexpression = null;
    {
      String _class_ = exp.getClass_();
      CharSequence _genClassConstraint = this.constraintGeneratorHelper.genClassConstraint(_class_, exp);
      this.buffer.append(_genClassConstraint);
      Type _methodBodyExpressionType = this.typeSystem.getMethodBodyExpressionType(exp);
      _xblockexpression = (_methodBodyExpressionType);
    }
    return _xblockexpression;
  }
  
  protected Type _genConstraintAndGetTypeCase(final Cast exp) {
    Type _xblockexpression = null;
    {
      StringConcatenation tempBuffer = this.buffer;
      StringConcatenation _stringConcatenation = new StringConcatenation();
      this.buffer = _stringConcatenation;
      Expression _object = exp.getObject();
      Type _genConstraintAndGetType = this.genConstraintAndGetType(_object);
      Type objectType = _genConstraintAndGetType;
      int _length = this.buffer.length();
      boolean _operator_greaterThan = IntegerExtensions.operator_greaterThan(_length, 0);
      if (_operator_greaterThan) {
        this.buffer.newLine();
      }
      tempBuffer.append(this.buffer);
      this.buffer = tempBuffer;
      String _type = exp.getType();
      CharSequence _genCastConstraint = this.constraintGeneratorHelper.genCastConstraint(_type, objectType, exp);
      this.buffer.append(_genCastConstraint);
      Type _methodBodyExpressionType = this.typeSystem.getMethodBodyExpressionType(exp);
      _xblockexpression = (_methodBodyExpressionType);
    }
    return _xblockexpression;
  }
  
  protected Type _genConstraintAndGetTypeCase(final Paren paren) {
    Expression _expression = paren.getExpression();
    Type _genConstraintAndGetTypeCase = this.genConstraintAndGetTypeCase(_expression);
    return _genConstraintAndGetTypeCase;
  }
  
  protected Type _genConstraintAndGetTypeCase(final VariableAccess variableAccess) {
    TypedDeclaration _variable = variableAccess.getVariable();
    Type _genConstraintAndGetTypeCase = this.genConstraintAndGetTypeCase(variableAccess, _variable);
    return _genConstraintAndGetTypeCase;
  }
  
  protected Type _genConstraintAndGetTypeCase(final VariableAccess variableAccess, final TypedDeclaration declaration) {
    TypeForDeclaration _type = declaration.getType();
    return _type;
  }
  
  protected Type _genConstraintAndGetTypeCase(final VariableAccess variableAccess, final Field field) {
    TypeForDeclaration _xblockexpression = null;
    {
      Type _thisType = this.typeSystem.getThisType(variableAccess);
      String _name = field.getName();
      TypeForDeclaration _type = field.getType();
      CharSequence _genFieldConstraint = this.constraintGeneratorHelper.genFieldConstraint(_thisType, _name, _type, variableAccess);
      this.buffer.append(_genFieldConstraint);
      TypeForDeclaration _type_1 = field.getType();
      _xblockexpression = (_type_1);
    }
    return _xblockexpression;
  }
  
  protected Type _genConstraintAndGetTypeCase(final Selection sel) {
    Type _xblockexpression = null;
    {
      StringConcatenation tempBuffer = this.buffer;
      StringConcatenation _stringConcatenation = new StringConcatenation();
      this.buffer = _stringConcatenation;
      Expression _receiver = sel.getReceiver();
      Type _genConstraintAndGetType = this.genConstraintAndGetType(_receiver);
      Type receiverType = _genConstraintAndGetType;
      int _length = this.buffer.length();
      boolean _operator_greaterThan = IntegerExtensions.operator_greaterThan(_length, 0);
      if (_operator_greaterThan) {
        this.buffer.newLine();
      }
      tempBuffer.append(this.buffer);
      this.buffer = tempBuffer;
      Message _message = sel.getMessage();
      Type _genConstraintAndGetTypeCase = this.genConstraintAndGetTypeCase(receiverType, _message, sel);
      _xblockexpression = (_genConstraintAndGetTypeCase);
    }
    return _xblockexpression;
  }
  
  protected Type _genConstraintAndGetTypeCase(final Type receiverType, final Message message, final Selection sel) {
    return null;
  }
  
  protected Type _genConstraintAndGetTypeCase(final Type receiverType, final FieldSelection fieldSel, final Selection sel) {
    TypeVariable _xblockexpression = null;
    {
      TypeVariable _createTypeVariable = this.typeSystem.createTypeVariable();
      TypeVariable fieldType = _createTypeVariable;
      String _field = fieldSel.getField();
      CharSequence _genFieldConstraint = this.constraintGeneratorHelper.genFieldConstraint(receiverType, _field, fieldType, sel);
      this.buffer.append(_genFieldConstraint);
      _xblockexpression = (fieldType);
    }
    return _xblockexpression;
  }
  
  protected Type _genConstraintAndGetTypeCase(final Type receiverType, final MethodCall methodCall, final Selection sel) {
    TypeVariable _xblockexpression = null;
    {
      TypeVariable _createTypeVariable = this.typeSystem.createTypeVariable();
      TypeVariable methodReturnType = _createTypeVariable;
      LinkedList<Type> _linkedList = new LinkedList<Type>();
      LinkedList<Type> typesForParams = _linkedList;
      EList<Expression> _args = methodCall.getArgs();
      for (final Expression arg : _args) {
        {
          TypeVariable _createTypeVariable_1 = this.typeSystem.createTypeVariable();
          TypeVariable typeForParam = _createTypeVariable_1;
          Type _genConstraintAndGetType = this.genConstraintAndGetType(arg);
          Type typeOfArg = _genConstraintAndGetType;
          this.buffer.newLineIfNotEmpty();
          typesForParams.add(typeForParam);
          CharSequence _genSubtypeConstraint = this.constraintGeneratorHelper.genSubtypeConstraint(typeOfArg, typeForParam, arg);
          this.buffer.append(_genSubtypeConstraint);
          this.buffer.newLineIfNotEmpty();
        }
      }
      String _method = methodCall.getMethod();
      CharSequence _genMethodConstraint = this.constraintGeneratorHelper.genMethodConstraint(receiverType, _method, methodReturnType, typesForParams, sel);
      this.buffer.append(_genMethodConstraint);
      _xblockexpression = (methodReturnType);
    }
    return _xblockexpression;
  }
  
  public Type genConstraintAndGetTypeCase(final Expression exp) {
    if (exp instanceof AndOrExpression) {
      return _genConstraintAndGetTypeCase((AndOrExpression)exp);
    } else if (exp instanceof ArithmeticSigned) {
      return _genConstraintAndGetTypeCase((ArithmeticSigned)exp);
    } else if (exp instanceof BooleanNegation) {
      return _genConstraintAndGetTypeCase((BooleanNegation)exp);
    } else if (exp instanceof Cast) {
      return _genConstraintAndGetTypeCase((Cast)exp);
    } else if (exp instanceof Comparison) {
      return _genConstraintAndGetTypeCase((Comparison)exp);
    } else if (exp instanceof Minus) {
      return _genConstraintAndGetTypeCase((Minus)exp);
    } else if (exp instanceof MultiOrDiv) {
      return _genConstraintAndGetTypeCase((MultiOrDiv)exp);
    } else if (exp instanceof New) {
      return _genConstraintAndGetTypeCase((New)exp);
    } else if (exp instanceof Paren) {
      return _genConstraintAndGetTypeCase((Paren)exp);
    } else if (exp instanceof Plus) {
      return _genConstraintAndGetTypeCase((Plus)exp);
    } else if (exp instanceof Selection) {
      return _genConstraintAndGetTypeCase((Selection)exp);
    } else if (exp instanceof VariableAccess) {
      return _genConstraintAndGetTypeCase((VariableAccess)exp);
    } else if (exp != null) {
      return _genConstraintAndGetTypeCase(exp);
    } else {
      throw new IllegalArgumentException("Unhandled parameter types: " +
        Arrays.<Object>asList(exp).toString());
    }
  }
  
  public Type genConstraintAndGetTypeCase(final VariableAccess variableAccess, final TypedDeclaration field) {
    if (field instanceof Field) {
      return _genConstraintAndGetTypeCase(variableAccess, (Field)field);
    } else if (field != null) {
      return _genConstraintAndGetTypeCase(variableAccess, field);
    } else {
      throw new IllegalArgumentException("Unhandled parameter types: " +
        Arrays.<Object>asList(variableAccess, field).toString());
    }
  }
  
  public Type genConstraintAndGetTypeCase(final Type receiverType, final Message fieldSel, final Selection sel) {
    if (fieldSel instanceof FieldSelection) {
      return _genConstraintAndGetTypeCase(receiverType, (FieldSelection)fieldSel, sel);
    } else if (fieldSel instanceof MethodCall) {
      return _genConstraintAndGetTypeCase(receiverType, (MethodCall)fieldSel, sel);
    } else if (fieldSel != null) {
      return _genConstraintAndGetTypeCase(receiverType, fieldSel, sel);
    } else {
      throw new IllegalArgumentException("Unhandled parameter types: " +
        Arrays.<Object>asList(receiverType, fieldSel, sel).toString());
    }
  }
}
