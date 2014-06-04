package org.deltaj.generator;

import com.google.inject.Inject;
import java.util.Arrays;
import java.util.List;
import org.deltaj.deltaj.Assignment;
import org.deltaj.deltaj.BooleanType;
import org.deltaj.deltaj.Expression;
import org.deltaj.deltaj.ExpressionStatement;
import org.deltaj.deltaj.IfStatement;
import org.deltaj.deltaj.Method;
import org.deltaj.deltaj.ReturnStatement;
import org.deltaj.deltaj.Statement;
import org.deltaj.deltaj.StatementBlock;
import org.deltaj.deltaj.Type;
import org.deltaj.deltaj.TypeForMethod;
import org.deltaj.generator.DeltaJConstraintGeneratorHelper;
import org.deltaj.generator.DeltaJExpressionConstraintGenerator;
import org.deltaj.generator.DeltaJGeneratorExtensions;
import org.deltaj.typing.DeltaJTypeSystem;
import org.deltaj.util.DeltaJTypeUtils;
import org.deltaj.util.DeltaJUtils;
import org.eclipse.emf.common.util.EList;
import org.eclipse.xtend2.lib.StringConcatenation;
import org.eclipse.xtext.xbase.lib.IntegerExtensions;
import org.eclipse.xtext.xbase.lib.ObjectExtensions;

@SuppressWarnings("all")
public class DeltaJStatementConstraintGenerator {
  private DeltaJTypeSystem typeSystem;
  
  @Inject
  private DeltaJExpressionConstraintGenerator expressionConstraintGenerator;
  
  @Inject
  private DeltaJConstraintGeneratorHelper constraintGeneratorHelper;
  
  @Inject
  private DeltaJGeneratorExtensions generatorExtensions;
  
  public CharSequence genConstraints(final DeltaJTypeSystem ts, final List<Statement> statements) {
    CharSequence _xblockexpression = null;
    {
      this.typeSystem = ts;
      CharSequence _genConstraints = this.genConstraints(statements);
      _xblockexpression = (_genConstraints);
    }
    return _xblockexpression;
  }
  
  public CharSequence genConstraints(final List<Statement> statements) {
    StringConcatenation _builder = new StringConcatenation();
    {
      for(final Statement statement : statements) {
        CharSequence _genConstraints = this.genConstraints(this.typeSystem, statement);
        _builder.append(_genConstraints, "");
        _builder.newLineIfNotEmpty();
      }
    }
    return _builder;
  }
  
  public CharSequence genConstraints(final DeltaJTypeSystem ts, final Statement statement) {
    CharSequence _xblockexpression = null;
    {
      this.typeSystem = ts;
      CharSequence _genConstraintsCase = this.genConstraintsCase(statement);
      CharSequence constraints = _genConstraintsCase;
      CharSequence _genComment = this.constraintGeneratorHelper.genComment(statement);
      CharSequence comment = _genComment;
      CharSequence _xifexpression = null;
      int _length = constraints.length();
      boolean _operator_greaterThan = IntegerExtensions.operator_greaterThan(_length, 0);
      if (_operator_greaterThan) {
        StringConcatenation _builder = new StringConcatenation();
        _builder.append(comment, "");
        _builder.newLineIfNotEmpty();
        _builder.append(constraints, "");
        _xifexpression = _builder;
      } else {
        _xifexpression = comment;
      }
      _xblockexpression = (_xifexpression);
    }
    return _xblockexpression;
  }
  
  protected CharSequence _genConstraintsCase(final Statement statement) {
    StringConcatenation _builder = new StringConcatenation();
    return _builder;
  }
  
  protected CharSequence _genConstraintsCase(final ExpressionStatement statement) {
    StringConcatenation _builder = new StringConcatenation();
    Expression _expression = statement.getExpression();
    StringConcatenation _genConstraints = this.expressionConstraintGenerator.genConstraints(this.typeSystem, _expression);
    _builder.append(_genConstraints, "");
    return _builder;
  }
  
  protected CharSequence _genConstraintsCase(final ReturnStatement statement) {
    CharSequence _xifexpression = null;
    Expression _expression = statement.getExpression();
    boolean _operator_notEquals = ObjectExtensions.operator_notEquals(_expression, null);
    if (_operator_notEquals) {
      StringConcatenation _xblockexpression = null;
      {
        StringConcatenation _stringConcatenation = new StringConcatenation();
        StringConcatenation buffer = _stringConcatenation;
        Expression _expression_1 = statement.getExpression();
        Type _genConstraintAndGetType = this.expressionConstraintGenerator.genConstraintAndGetType(this.typeSystem, buffer, _expression_1);
        final Type expType = _genConstraintAndGetType;
        this.generatorExtensions.addNewLineIfNotEmpty(buffer);
        Method _containingMethod = DeltaJUtils.getContainingMethod(statement);
        TypeForMethod _returntype = _containingMethod.getReturntype();
        Expression _expression_2 = statement.getExpression();
        CharSequence _genSubtypeConstraint = this.constraintGeneratorHelper.genSubtypeConstraint(expType, _returntype, _expression_2);
        buffer.append(_genSubtypeConstraint);
        _xblockexpression = (buffer);
      }
      _xifexpression = _xblockexpression;
    } else {
      StringConcatenation _builder = new StringConcatenation();
      _xifexpression = _builder;
    }
    return _xifexpression;
  }
  
  protected CharSequence _genConstraintsCase(final Assignment assignment) {
    StringConcatenation _xblockexpression = null;
    {
      StringConcatenation _stringConcatenation = new StringConcatenation();
      StringConcatenation buffer = _stringConcatenation;
      this.expressionConstraintGenerator.init(this.typeSystem, buffer);
      Expression _left = assignment.getLeft();
      Type _genConstraintAndGetType = this.expressionConstraintGenerator.genConstraintAndGetType(_left);
      Type leftType = _genConstraintAndGetType;
      this.generatorExtensions.addNewLineIfNotEmpty(buffer);
      Expression _right = assignment.getRight();
      Type _genConstraintAndGetType_1 = this.expressionConstraintGenerator.genConstraintAndGetType(_right);
      Type rightType = _genConstraintAndGetType_1;
      this.generatorExtensions.addNewLineIfNotEmpty(buffer);
      Expression _right_1 = assignment.getRight();
      CharSequence _genSubtypeConstraint = this.constraintGeneratorHelper.genSubtypeConstraint(rightType, leftType, _right_1);
      buffer.append(_genSubtypeConstraint);
      _xblockexpression = (buffer);
    }
    return _xblockexpression;
  }
  
  protected CharSequence _genConstraintsCase(final IfStatement statement) {
    StringConcatenation _xblockexpression = null;
    {
      StringConcatenation _stringConcatenation = new StringConcatenation();
      StringConcatenation buffer = _stringConcatenation;
      Expression _expression = statement.getExpression();
      Type _genConstraintAndGetType = this.expressionConstraintGenerator.genConstraintAndGetType(this.typeSystem, buffer, _expression);
      Type expressionType = _genConstraintAndGetType;
      BooleanType _createBooleanType = DeltaJTypeUtils.createBooleanType();
      BooleanType booleanType = _createBooleanType;
      this.generatorExtensions.addNewLineIfNotEmpty(buffer);
      Expression _expression_1 = statement.getExpression();
      CharSequence _genSubtypeConstraint = this.constraintGeneratorHelper.genSubtypeConstraint(expressionType, booleanType, _expression_1);
      buffer.append(_genSubtypeConstraint);
      this.generatorExtensions.addNewLineIfNotEmpty(buffer);
      StringConcatenation _builder = new StringConcatenation();
      _builder.append("// then branch");
      buffer.append(_builder);
      this.generatorExtensions.addNewLineIfNotEmpty(buffer);
      StatementBlock _thenBlock = statement.getThenBlock();
      EList<Statement> _statements = _thenBlock.getStatements();
      CharSequence _genConstraints = this.genConstraints(_statements);
      buffer.append(_genConstraints);
      StatementBlock _elseBlock = statement.getElseBlock();
      boolean _operator_notEquals = ObjectExtensions.operator_notEquals(_elseBlock, null);
      if (_operator_notEquals) {
        {
          buffer.newLineIfNotEmpty();
          StringConcatenation _builder_1 = new StringConcatenation();
          _builder_1.append("// else branch");
          buffer.append(_builder_1);
          this.generatorExtensions.addNewLineIfNotEmpty(buffer);
          StatementBlock _elseBlock_1 = statement.getElseBlock();
          EList<Statement> _statements_1 = _elseBlock_1.getStatements();
          CharSequence _genConstraints_1 = this.genConstraints(_statements_1);
          buffer.append(_genConstraints_1);
        }
      }
      _xblockexpression = (buffer);
    }
    return _xblockexpression;
  }
  
  public StringConcatenation genConstraints(final Expression exp) {
    StringConcatenation _genConstraints = this.expressionConstraintGenerator.genConstraints(this.typeSystem, exp);
    return _genConstraints;
  }
  
  public CharSequence genConstraintsCase(final Statement assignment) {
    if (assignment instanceof Assignment) {
      return _genConstraintsCase((Assignment)assignment);
    } else if (assignment instanceof ExpressionStatement) {
      return _genConstraintsCase((ExpressionStatement)assignment);
    } else if (assignment instanceof IfStatement) {
      return _genConstraintsCase((IfStatement)assignment);
    } else if (assignment instanceof ReturnStatement) {
      return _genConstraintsCase((ReturnStatement)assignment);
    } else if (assignment != null) {
      return _genConstraintsCase(assignment);
    } else {
      throw new IllegalArgumentException("Unhandled parameter types: " +
        Arrays.<Object>asList(assignment).toString());
    }
  }
}
