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
import org.deltaj.typing.DeltaJTypeSystem;
import org.deltaj.util.DeltaJTypeUtils;
import org.eclipse.emf.common.util.EList;
import org.eclipse.xtend2.lib.StringConcatenation;
import org.eclipse.xtext.xbase.lib.XbaseGenerated;

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
      _xblockexpression = this.buffer;
    }
    return _xblockexpression;
  }

  public Type genConstraintAndGetType(final DeltaJTypeSystem ts, final StringConcatenation buffer, final Expression exp) {
    Type _xblockexpression = null;
    {
      this.init(ts, buffer);
      _xblockexpression = this.genConstraintAndGetType(exp);
    }
    return _xblockexpression;
  }

  public Type genConstraintAndGetType(final Expression exp) {
    return this.genConstraintAndGetTypeCase(exp);
  }

  protected Type _genConstraintAndGetTypeCase(final Expression exp) {
    return this.typeSystem.getMethodBodyExpressionType(exp);
  }

  protected Type _genConstraintAndGetTypeCase(final Plus exp) {
    TypeVariable _xblockexpression = null;
    {
      Type leftType = this.genConstraintAndGetType(exp.getLeft());
      this.buffer.newLineIfNotEmpty();
      Type rightType = this.genConstraintAndGetType(exp.getRight());
      this.buffer.newLineIfNotEmpty();
      TypeVariable plusType = this.typeSystem.createTypeVariable();
      this.buffer.append(this.constraintGeneratorHelper.genPlusConstraint(leftType, rightType, plusType, exp));
      _xblockexpression = plusType;
    }
    return _xblockexpression;
  }

  protected Type _genConstraintAndGetTypeCase(final Minus exp) {
    IntType _xblockexpression = null;
    {
      IntType intType = DeltaJTypeUtils.createIntType();
      this.genConstraintsForSubexpressions(exp, exp.getLeft(), exp.getRight(), intType);
      _xblockexpression = intType;
    }
    return _xblockexpression;
  }

  protected Type _genConstraintAndGetTypeCase(final MultiOrDiv exp) {
    IntType _xblockexpression = null;
    {
      IntType intType = DeltaJTypeUtils.createIntType();
      this.genConstraintsForSubexpressions(exp, exp.getLeft(), exp.getRight(), intType);
      _xblockexpression = intType;
    }
    return _xblockexpression;
  }

  protected Type _genConstraintAndGetTypeCase(final AndOrExpression exp) {
    BooleanType _xblockexpression = null;
    {
      BooleanType booleanType = DeltaJTypeUtils.createBooleanType();
      this.genConstraintsForSubexpressions(exp, exp.getLeft(), exp.getRight(), booleanType);
      _xblockexpression = booleanType;
    }
    return _xblockexpression;
  }

  protected Type _genConstraintAndGetTypeCase(final Comparison exp) {
    BooleanType _xblockexpression = null;
    {
      BooleanType booleanType = DeltaJTypeUtils.createBooleanType();
      this.genConstraintsForSubexpressions(exp, exp.getLeft(), exp.getRight(), DeltaJTypeUtils.createIntType());
      _xblockexpression = booleanType;
    }
    return _xblockexpression;
  }

  public void genConstraintsForSubexpressions(final Expression main, final Expression left, final Expression right, final Type expectedType) {
    Type leftType = this.genConstraintAndGetType(left);
    this.buffer.newLineIfNotEmpty();
    this.buffer.append(this.constraintGeneratorHelper.genSubtypeConstraint(leftType, expectedType, left));
    this.buffer.newLineIfNotEmpty();
    Type rightType = this.genConstraintAndGetType(right);
    this.buffer.newLineIfNotEmpty();
    this.buffer.append(this.constraintGeneratorHelper.genSubtypeConstraint(rightType, expectedType, right));
    this.buffer.newLineIfNotEmpty();
    this.buffer.append(this.constraintGeneratorHelper.genComment(main));
  }

  protected Type _genConstraintAndGetTypeCase(final ArithmeticSigned exp) {
    IntType _xblockexpression = null;
    {
      IntType intType = DeltaJTypeUtils.createIntType();
      this.genConstraintsForSubexpressions(exp, exp.getExpression(), intType);
      _xblockexpression = intType;
    }
    return _xblockexpression;
  }

  protected Type _genConstraintAndGetTypeCase(final BooleanNegation exp) {
    BooleanType _xblockexpression = null;
    {
      BooleanType booleanType = DeltaJTypeUtils.createBooleanType();
      this.genConstraintsForSubexpressions(exp, exp.getExpression(), booleanType);
      _xblockexpression = booleanType;
    }
    return _xblockexpression;
  }

  public void genConstraintsForSubexpressions(final Expression main, final Expression subExp, final Type expectedType) {
    Type subExpType = this.genConstraintAndGetType(subExp);
    this.buffer.newLineIfNotEmpty();
    this.buffer.append(this.constraintGeneratorHelper.genSubtypeConstraint(subExpType, expectedType, subExp));
    this.buffer.newLineIfNotEmpty();
    this.buffer.append(this.constraintGeneratorHelper.genComment(main));
  }

  protected Type _genConstraintAndGetTypeCase(final New exp) {
    Type _xblockexpression = null;
    {
      this.buffer.append(this.constraintGeneratorHelper.genClassConstraint(exp.getClass_(), exp));
      _xblockexpression = this.typeSystem.getMethodBodyExpressionType(exp);
    }
    return _xblockexpression;
  }

  protected Type _genConstraintAndGetTypeCase(final Cast exp) {
    Type _xblockexpression = null;
    {
      StringConcatenation tempBuffer = this.buffer;
      StringConcatenation _stringConcatenation = new StringConcatenation();
      this.buffer = _stringConcatenation;
      Type objectType = this.genConstraintAndGetType(exp.getObject());
      int _length = this.buffer.length();
      boolean _greaterThan = (_length > 0);
      if (_greaterThan) {
        this.buffer.newLine();
      }
      tempBuffer.append(this.buffer);
      this.buffer = tempBuffer;
      this.buffer.append(this.constraintGeneratorHelper.genCastConstraint(exp.getType(), objectType, exp));
      _xblockexpression = this.typeSystem.getMethodBodyExpressionType(exp);
    }
    return _xblockexpression;
  }

  protected Type _genConstraintAndGetTypeCase(final Paren paren) {
    return this.genConstraintAndGetTypeCase(paren.getExpression());
  }

  protected Type _genConstraintAndGetTypeCase(final VariableAccess variableAccess) {
    return this.genConstraintAndGetTypeCase(variableAccess, variableAccess.getVariable());
  }

  protected Type _genConstraintAndGetTypeCase(final VariableAccess variableAccess, final TypedDeclaration declaration) {
    return declaration.getType();
  }

  protected Type _genConstraintAndGetTypeCase(final VariableAccess variableAccess, final Field field) {
    TypeForDeclaration _xblockexpression = null;
    {
      this.buffer.append(
        this.constraintGeneratorHelper.genFieldConstraint(this.typeSystem.getThisType(variableAccess), field.getName(), field.getType(), variableAccess));
      _xblockexpression = field.getType();
    }
    return _xblockexpression;
  }

  protected Type _genConstraintAndGetTypeCase(final Selection sel) {
    Type _xblockexpression = null;
    {
      StringConcatenation tempBuffer = this.buffer;
      StringConcatenation _stringConcatenation = new StringConcatenation();
      this.buffer = _stringConcatenation;
      Type receiverType = this.genConstraintAndGetType(sel.getReceiver());
      int _length = this.buffer.length();
      boolean _greaterThan = (_length > 0);
      if (_greaterThan) {
        this.buffer.newLine();
      }
      tempBuffer.append(this.buffer);
      this.buffer = tempBuffer;
      _xblockexpression = this.genConstraintAndGetTypeCase(receiverType, sel.getMessage(), sel);
    }
    return _xblockexpression;
  }

  protected Type _genConstraintAndGetTypeCase(final Type receiverType, final Message message, final Selection sel) {
    return null;
  }

  protected Type _genConstraintAndGetTypeCase(final Type receiverType, final FieldSelection fieldSel, final Selection sel) {
    TypeVariable _xblockexpression = null;
    {
      TypeVariable fieldType = this.typeSystem.createTypeVariable();
      this.buffer.append(this.constraintGeneratorHelper.genFieldConstraint(receiverType, fieldSel.getField(), fieldType, sel));
      _xblockexpression = fieldType;
    }
    return _xblockexpression;
  }

  protected Type _genConstraintAndGetTypeCase(final Type receiverType, final MethodCall methodCall, final Selection sel) {
    TypeVariable _xblockexpression = null;
    {
      TypeVariable methodReturnType = this.typeSystem.createTypeVariable();
      LinkedList<Type> typesForParams = new LinkedList<Type>();
      EList<Expression> _args = methodCall.getArgs();
      for (final Expression arg : _args) {
        {
          TypeVariable typeForParam = this.typeSystem.createTypeVariable();
          Type typeOfArg = this.genConstraintAndGetType(arg);
          this.buffer.newLineIfNotEmpty();
          typesForParams.add(typeForParam);
          this.buffer.append(this.constraintGeneratorHelper.genSubtypeConstraint(typeOfArg, typeForParam, arg));
          this.buffer.newLineIfNotEmpty();
        }
      }
      this.buffer.append(this.constraintGeneratorHelper.genMethodConstraint(receiverType, methodCall.getMethod(), methodReturnType, typesForParams, sel));
      _xblockexpression = methodReturnType;
    }
    return _xblockexpression;
  }

  @XbaseGenerated
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

  @XbaseGenerated
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

  @XbaseGenerated
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
