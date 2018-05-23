/**
 * <copyright>
 * </copyright>
 *
 */
package org.deltaj.deltaj.util;

import org.deltaj.deltaj.And;
import org.deltaj.deltaj.AndOrExpression;
import org.deltaj.deltaj.ArithmeticSigned;
import org.deltaj.deltaj.Assignment;
import org.deltaj.deltaj.BasicType;
import org.deltaj.deltaj.BoolConstant;
import org.deltaj.deltaj.BooleanNegation;
import org.deltaj.deltaj.BooleanType;
import org.deltaj.deltaj.Cast;
import org.deltaj.deltaj.ClassAddition;
import org.deltaj.deltaj.ClassModification;
import org.deltaj.deltaj.ClassRemoval;
import org.deltaj.deltaj.ClassType;
import org.deltaj.deltaj.Comparison;
import org.deltaj.deltaj.Configuration;
import org.deltaj.deltaj.Configurations;
import org.deltaj.deltaj.Constant;
import org.deltaj.deltaj.DeltaAction;
import org.deltaj.deltaj.DeltaModule;
import org.deltaj.deltaj.DeltaPartition;
import org.deltaj.deltaj.DeltaSubAction;
import org.deltaj.deltaj.DeltajPackage;
import org.deltaj.deltaj.Expression;
import org.deltaj.deltaj.ExpressionStatement;
import org.deltaj.deltaj.Feature;
import org.deltaj.deltaj.FeatureRef;
import org.deltaj.deltaj.Features;
import org.deltaj.deltaj.Field;
import org.deltaj.deltaj.FieldAddition;
import org.deltaj.deltaj.FieldRemoval;
import org.deltaj.deltaj.FieldSelection;
import org.deltaj.deltaj.IfStatement;
import org.deltaj.deltaj.IntConstant;
import org.deltaj.deltaj.IntType;
import org.deltaj.deltaj.JavaVerbatim;
import org.deltaj.deltaj.LocalVariableDeclaration;
import org.deltaj.deltaj.Message;
import org.deltaj.deltaj.Method;
import org.deltaj.deltaj.MethodAddition;
import org.deltaj.deltaj.MethodCall;
import org.deltaj.deltaj.MethodModification;
import org.deltaj.deltaj.MethodOrFieldAddition;
import org.deltaj.deltaj.MethodRemoval;
import org.deltaj.deltaj.Minus;
import org.deltaj.deltaj.ModuleReference;
import org.deltaj.deltaj.MultiOrDiv;
import org.deltaj.deltaj.Negation;
import org.deltaj.deltaj.New;
import org.deltaj.deltaj.Null;
import org.deltaj.deltaj.Or;
import org.deltaj.deltaj.Original;
import org.deltaj.deltaj.Parameter;
import org.deltaj.deltaj.Paren;
import org.deltaj.deltaj.PartitionPart;
import org.deltaj.deltaj.Plus;
import org.deltaj.deltaj.Product;
import org.deltaj.deltaj.ProductLine;
import org.deltaj.deltaj.Program;
import org.deltaj.deltaj.PropFalse;
import org.deltaj.deltaj.PropParen;
import org.deltaj.deltaj.PropTrue;
import org.deltaj.deltaj.PropositionalFormula;
import org.deltaj.deltaj.RemovesOrModifiesClass;
import org.deltaj.deltaj.ReturnStatement;
import org.deltaj.deltaj.Selection;
import org.deltaj.deltaj.Statement;
import org.deltaj.deltaj.StatementBlock;
import org.deltaj.deltaj.StringConstant;
import org.deltaj.deltaj.StringType;
import org.deltaj.deltaj.This;
import org.deltaj.deltaj.Type;
import org.deltaj.deltaj.TypeForDeclaration;
import org.deltaj.deltaj.TypeForMethod;
import org.deltaj.deltaj.TypeVariable;
import org.deltaj.deltaj.TypedDeclaration;
import org.deltaj.deltaj.VariableAccess;
import org.deltaj.deltaj.VoidType;

import org.eclipse.emf.common.notify.Adapter;
import org.eclipse.emf.common.notify.Notifier;

import org.eclipse.emf.common.notify.impl.AdapterFactoryImpl;

import org.eclipse.emf.ecore.EObject;

/**
 * <!-- begin-user-doc -->
 * The <b>Adapter Factory</b> for the model.
 * It provides an adapter <code>createXXX</code> method for each class of the model.
 * <!-- end-user-doc -->
 * @see org.deltaj.deltaj.DeltajPackage
 * @generated
 */
public class DeltajAdapterFactory extends AdapterFactoryImpl
{
  /**
   * The cached model package.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  protected static DeltajPackage modelPackage;

  /**
   * Creates an instance of the adapter factory.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public DeltajAdapterFactory()
  {
    if (modelPackage == null)
    {
      modelPackage = DeltajPackage.eINSTANCE;
    }
  }

  /**
   * Returns whether this factory is applicable for the type of the object.
   * <!-- begin-user-doc -->
   * This implementation returns <code>true</code> if the object is either the model's package or is an instance object of the model.
   * <!-- end-user-doc -->
   * @return whether this factory is applicable for the type of the object.
   * @generated
   */
  @Override
  public boolean isFactoryForType(Object object)
  {
    if (object == modelPackage)
    {
      return true;
    }
    if (object instanceof EObject)
    {
      return ((EObject)object).eClass().getEPackage() == modelPackage;
    }
    return false;
  }

  /**
   * The switch that delegates to the <code>createXXX</code> methods.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  protected DeltajSwitch<Adapter> modelSwitch =
    new DeltajSwitch<Adapter>()
    {
      @Override
      public Adapter caseProgram(Program object)
      {
        return createProgramAdapter();
      }
      @Override
      public Adapter caseType(Type object)
      {
        return createTypeAdapter();
      }
      @Override
      public Adapter caseTypeVariable(TypeVariable object)
      {
        return createTypeVariableAdapter();
      }
      @Override
      public Adapter caseTypeForMethod(TypeForMethod object)
      {
        return createTypeForMethodAdapter();
      }
      @Override
      public Adapter caseVoidType(VoidType object)
      {
        return createVoidTypeAdapter();
      }
      @Override
      public Adapter caseTypeForDeclaration(TypeForDeclaration object)
      {
        return createTypeForDeclarationAdapter();
      }
      @Override
      public Adapter caseBasicType(BasicType object)
      {
        return createBasicTypeAdapter();
      }
      @Override
      public Adapter caseIntType(IntType object)
      {
        return createIntTypeAdapter();
      }
      @Override
      public Adapter caseBooleanType(BooleanType object)
      {
        return createBooleanTypeAdapter();
      }
      @Override
      public Adapter caseStringType(StringType object)
      {
        return createStringTypeAdapter();
      }
      @Override
      public Adapter caseClassType(ClassType object)
      {
        return createClassTypeAdapter();
      }
      @Override
      public Adapter caseClass(org.deltaj.deltaj.Class object)
      {
        return createClassAdapter();
      }
      @Override
      public Adapter caseTypedDeclaration(TypedDeclaration object)
      {
        return createTypedDeclarationAdapter();
      }
      @Override
      public Adapter caseField(Field object)
      {
        return createFieldAdapter();
      }
      @Override
      public Adapter caseLocalVariableDeclaration(LocalVariableDeclaration object)
      {
        return createLocalVariableDeclarationAdapter();
      }
      @Override
      public Adapter caseParameter(Parameter object)
      {
        return createParameterAdapter();
      }
      @Override
      public Adapter caseMethod(Method object)
      {
        return createMethodAdapter();
      }
      @Override
      public Adapter caseStatementBlock(StatementBlock object)
      {
        return createStatementBlockAdapter();
      }
      @Override
      public Adapter caseStatement(Statement object)
      {
        return createStatementAdapter();
      }
      @Override
      public Adapter caseExpressionStatement(ExpressionStatement object)
      {
        return createExpressionStatementAdapter();
      }
      @Override
      public Adapter caseAssignment(Assignment object)
      {
        return createAssignmentAdapter();
      }
      @Override
      public Adapter caseIfStatement(IfStatement object)
      {
        return createIfStatementAdapter();
      }
      @Override
      public Adapter caseExpression(Expression object)
      {
        return createExpressionAdapter();
      }
      @Override
      public Adapter caseNull(Null object)
      {
        return createNullAdapter();
      }
      @Override
      public Adapter caseThis(This object)
      {
        return createThisAdapter();
      }
      @Override
      public Adapter caseOriginal(Original object)
      {
        return createOriginalAdapter();
      }
      @Override
      public Adapter caseVariableAccess(VariableAccess object)
      {
        return createVariableAccessAdapter();
      }
      @Override
      public Adapter caseNew(New object)
      {
        return createNewAdapter();
      }
      @Override
      public Adapter caseCast(Cast object)
      {
        return createCastAdapter();
      }
      @Override
      public Adapter caseParen(Paren object)
      {
        return createParenAdapter();
      }
      @Override
      public Adapter caseConstant(Constant object)
      {
        return createConstantAdapter();
      }
      @Override
      public Adapter caseStringConstant(StringConstant object)
      {
        return createStringConstantAdapter();
      }
      @Override
      public Adapter caseIntConstant(IntConstant object)
      {
        return createIntConstantAdapter();
      }
      @Override
      public Adapter caseBoolConstant(BoolConstant object)
      {
        return createBoolConstantAdapter();
      }
      @Override
      public Adapter caseMessage(Message object)
      {
        return createMessageAdapter();
      }
      @Override
      public Adapter caseMethodCall(MethodCall object)
      {
        return createMethodCallAdapter();
      }
      @Override
      public Adapter caseFieldSelection(FieldSelection object)
      {
        return createFieldSelectionAdapter();
      }
      @Override
      public Adapter caseDeltaModule(DeltaModule object)
      {
        return createDeltaModuleAdapter();
      }
      @Override
      public Adapter caseDeltaAction(DeltaAction object)
      {
        return createDeltaActionAdapter();
      }
      @Override
      public Adapter caseClassAddition(ClassAddition object)
      {
        return createClassAdditionAdapter();
      }
      @Override
      public Adapter caseRemovesOrModifiesClass(RemovesOrModifiesClass object)
      {
        return createRemovesOrModifiesClassAdapter();
      }
      @Override
      public Adapter caseClassRemoval(ClassRemoval object)
      {
        return createClassRemovalAdapter();
      }
      @Override
      public Adapter caseClassModification(ClassModification object)
      {
        return createClassModificationAdapter();
      }
      @Override
      public Adapter caseDeltaSubAction(DeltaSubAction object)
      {
        return createDeltaSubActionAdapter();
      }
      @Override
      public Adapter caseMethodOrFieldAddition(MethodOrFieldAddition object)
      {
        return createMethodOrFieldAdditionAdapter();
      }
      @Override
      public Adapter caseFieldAddition(FieldAddition object)
      {
        return createFieldAdditionAdapter();
      }
      @Override
      public Adapter caseMethodAddition(MethodAddition object)
      {
        return createMethodAdditionAdapter();
      }
      @Override
      public Adapter caseFieldRemoval(FieldRemoval object)
      {
        return createFieldRemovalAdapter();
      }
      @Override
      public Adapter caseMethodRemoval(MethodRemoval object)
      {
        return createMethodRemovalAdapter();
      }
      @Override
      public Adapter caseMethodModification(MethodModification object)
      {
        return createMethodModificationAdapter();
      }
      @Override
      public Adapter caseProductLine(ProductLine object)
      {
        return createProductLineAdapter();
      }
      @Override
      public Adapter caseFeatures(Features object)
      {
        return createFeaturesAdapter();
      }
      @Override
      public Adapter caseFeature(Feature object)
      {
        return createFeatureAdapter();
      }
      @Override
      public Adapter caseConfigurations(Configurations object)
      {
        return createConfigurationsAdapter();
      }
      @Override
      public Adapter caseConfiguration(Configuration object)
      {
        return createConfigurationAdapter();
      }
      @Override
      public Adapter caseDeltaPartition(DeltaPartition object)
      {
        return createDeltaPartitionAdapter();
      }
      @Override
      public Adapter casePartitionPart(PartitionPart object)
      {
        return createPartitionPartAdapter();
      }
      @Override
      public Adapter caseModuleReference(ModuleReference object)
      {
        return createModuleReferenceAdapter();
      }
      @Override
      public Adapter casePropositionalFormula(PropositionalFormula object)
      {
        return createPropositionalFormulaAdapter();
      }
      @Override
      public Adapter caseProduct(Product object)
      {
        return createProductAdapter();
      }
      @Override
      public Adapter caseReturnStatement(ReturnStatement object)
      {
        return createReturnStatementAdapter();
      }
      @Override
      public Adapter caseJavaVerbatim(JavaVerbatim object)
      {
        return createJavaVerbatimAdapter();
      }
      @Override
      public Adapter casePlus(Plus object)
      {
        return createPlusAdapter();
      }
      @Override
      public Adapter caseMinus(Minus object)
      {
        return createMinusAdapter();
      }
      @Override
      public Adapter caseMultiOrDiv(MultiOrDiv object)
      {
        return createMultiOrDivAdapter();
      }
      @Override
      public Adapter caseComparison(Comparison object)
      {
        return createComparisonAdapter();
      }
      @Override
      public Adapter caseAndOrExpression(AndOrExpression object)
      {
        return createAndOrExpressionAdapter();
      }
      @Override
      public Adapter caseBooleanNegation(BooleanNegation object)
      {
        return createBooleanNegationAdapter();
      }
      @Override
      public Adapter caseArithmeticSigned(ArithmeticSigned object)
      {
        return createArithmeticSignedAdapter();
      }
      @Override
      public Adapter caseSelection(Selection object)
      {
        return createSelectionAdapter();
      }
      @Override
      public Adapter caseOr(Or object)
      {
        return createOrAdapter();
      }
      @Override
      public Adapter caseAnd(And object)
      {
        return createAndAdapter();
      }
      @Override
      public Adapter caseFeatureRef(FeatureRef object)
      {
        return createFeatureRefAdapter();
      }
      @Override
      public Adapter casePropParen(PropParen object)
      {
        return createPropParenAdapter();
      }
      @Override
      public Adapter caseNegation(Negation object)
      {
        return createNegationAdapter();
      }
      @Override
      public Adapter casePropTrue(PropTrue object)
      {
        return createPropTrueAdapter();
      }
      @Override
      public Adapter casePropFalse(PropFalse object)
      {
        return createPropFalseAdapter();
      }
      @Override
      public Adapter defaultCase(EObject object)
      {
        return createEObjectAdapter();
      }
    };

  /**
   * Creates an adapter for the <code>target</code>.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @param target the object to adapt.
   * @return the adapter for the <code>target</code>.
   * @generated
   */
  @Override
  public Adapter createAdapter(Notifier target)
  {
    return modelSwitch.doSwitch((EObject)target);
  }


  /**
   * Creates a new adapter for an object of class '{@link org.deltaj.deltaj.Program <em>Program</em>}'.
   * <!-- begin-user-doc -->
   * This default implementation returns null so that we can easily ignore cases;
   * it's useful to ignore a case when inheritance will catch all the cases anyway.
   * <!-- end-user-doc -->
   * @return the new adapter.
   * @see org.deltaj.deltaj.Program
   * @generated
   */
  public Adapter createProgramAdapter()
  {
    return null;
  }

  /**
   * Creates a new adapter for an object of class '{@link org.deltaj.deltaj.Type <em>Type</em>}'.
   * <!-- begin-user-doc -->
   * This default implementation returns null so that we can easily ignore cases;
   * it's useful to ignore a case when inheritance will catch all the cases anyway.
   * <!-- end-user-doc -->
   * @return the new adapter.
   * @see org.deltaj.deltaj.Type
   * @generated
   */
  public Adapter createTypeAdapter()
  {
    return null;
  }

  /**
   * Creates a new adapter for an object of class '{@link org.deltaj.deltaj.TypeVariable <em>Type Variable</em>}'.
   * <!-- begin-user-doc -->
   * This default implementation returns null so that we can easily ignore cases;
   * it's useful to ignore a case when inheritance will catch all the cases anyway.
   * <!-- end-user-doc -->
   * @return the new adapter.
   * @see org.deltaj.deltaj.TypeVariable
   * @generated
   */
  public Adapter createTypeVariableAdapter()
  {
    return null;
  }

  /**
   * Creates a new adapter for an object of class '{@link org.deltaj.deltaj.TypeForMethod <em>Type For Method</em>}'.
   * <!-- begin-user-doc -->
   * This default implementation returns null so that we can easily ignore cases;
   * it's useful to ignore a case when inheritance will catch all the cases anyway.
   * <!-- end-user-doc -->
   * @return the new adapter.
   * @see org.deltaj.deltaj.TypeForMethod
   * @generated
   */
  public Adapter createTypeForMethodAdapter()
  {
    return null;
  }

  /**
   * Creates a new adapter for an object of class '{@link org.deltaj.deltaj.VoidType <em>Void Type</em>}'.
   * <!-- begin-user-doc -->
   * This default implementation returns null so that we can easily ignore cases;
   * it's useful to ignore a case when inheritance will catch all the cases anyway.
   * <!-- end-user-doc -->
   * @return the new adapter.
   * @see org.deltaj.deltaj.VoidType
   * @generated
   */
  public Adapter createVoidTypeAdapter()
  {
    return null;
  }

  /**
   * Creates a new adapter for an object of class '{@link org.deltaj.deltaj.TypeForDeclaration <em>Type For Declaration</em>}'.
   * <!-- begin-user-doc -->
   * This default implementation returns null so that we can easily ignore cases;
   * it's useful to ignore a case when inheritance will catch all the cases anyway.
   * <!-- end-user-doc -->
   * @return the new adapter.
   * @see org.deltaj.deltaj.TypeForDeclaration
   * @generated
   */
  public Adapter createTypeForDeclarationAdapter()
  {
    return null;
  }

  /**
   * Creates a new adapter for an object of class '{@link org.deltaj.deltaj.BasicType <em>Basic Type</em>}'.
   * <!-- begin-user-doc -->
   * This default implementation returns null so that we can easily ignore cases;
   * it's useful to ignore a case when inheritance will catch all the cases anyway.
   * <!-- end-user-doc -->
   * @return the new adapter.
   * @see org.deltaj.deltaj.BasicType
   * @generated
   */
  public Adapter createBasicTypeAdapter()
  {
    return null;
  }

  /**
   * Creates a new adapter for an object of class '{@link org.deltaj.deltaj.IntType <em>Int Type</em>}'.
   * <!-- begin-user-doc -->
   * This default implementation returns null so that we can easily ignore cases;
   * it's useful to ignore a case when inheritance will catch all the cases anyway.
   * <!-- end-user-doc -->
   * @return the new adapter.
   * @see org.deltaj.deltaj.IntType
   * @generated
   */
  public Adapter createIntTypeAdapter()
  {
    return null;
  }

  /**
   * Creates a new adapter for an object of class '{@link org.deltaj.deltaj.BooleanType <em>Boolean Type</em>}'.
   * <!-- begin-user-doc -->
   * This default implementation returns null so that we can easily ignore cases;
   * it's useful to ignore a case when inheritance will catch all the cases anyway.
   * <!-- end-user-doc -->
   * @return the new adapter.
   * @see org.deltaj.deltaj.BooleanType
   * @generated
   */
  public Adapter createBooleanTypeAdapter()
  {
    return null;
  }

  /**
   * Creates a new adapter for an object of class '{@link org.deltaj.deltaj.StringType <em>String Type</em>}'.
   * <!-- begin-user-doc -->
   * This default implementation returns null so that we can easily ignore cases;
   * it's useful to ignore a case when inheritance will catch all the cases anyway.
   * <!-- end-user-doc -->
   * @return the new adapter.
   * @see org.deltaj.deltaj.StringType
   * @generated
   */
  public Adapter createStringTypeAdapter()
  {
    return null;
  }

  /**
   * Creates a new adapter for an object of class '{@link org.deltaj.deltaj.ClassType <em>Class Type</em>}'.
   * <!-- begin-user-doc -->
   * This default implementation returns null so that we can easily ignore cases;
   * it's useful to ignore a case when inheritance will catch all the cases anyway.
   * <!-- end-user-doc -->
   * @return the new adapter.
   * @see org.deltaj.deltaj.ClassType
   * @generated
   */
  public Adapter createClassTypeAdapter()
  {
    return null;
  }

  /**
   * Creates a new adapter for an object of class '{@link org.deltaj.deltaj.Class <em>Class</em>}'.
   * <!-- begin-user-doc -->
   * This default implementation returns null so that we can easily ignore cases;
   * it's useful to ignore a case when inheritance will catch all the cases anyway.
   * <!-- end-user-doc -->
   * @return the new adapter.
   * @see org.deltaj.deltaj.Class
   * @generated
   */
  public Adapter createClassAdapter()
  {
    return null;
  }

  /**
   * Creates a new adapter for an object of class '{@link org.deltaj.deltaj.TypedDeclaration <em>Typed Declaration</em>}'.
   * <!-- begin-user-doc -->
   * This default implementation returns null so that we can easily ignore cases;
   * it's useful to ignore a case when inheritance will catch all the cases anyway.
   * <!-- end-user-doc -->
   * @return the new adapter.
   * @see org.deltaj.deltaj.TypedDeclaration
   * @generated
   */
  public Adapter createTypedDeclarationAdapter()
  {
    return null;
  }

  /**
   * Creates a new adapter for an object of class '{@link org.deltaj.deltaj.Field <em>Field</em>}'.
   * <!-- begin-user-doc -->
   * This default implementation returns null so that we can easily ignore cases;
   * it's useful to ignore a case when inheritance will catch all the cases anyway.
   * <!-- end-user-doc -->
   * @return the new adapter.
   * @see org.deltaj.deltaj.Field
   * @generated
   */
  public Adapter createFieldAdapter()
  {
    return null;
  }

  /**
   * Creates a new adapter for an object of class '{@link org.deltaj.deltaj.LocalVariableDeclaration <em>Local Variable Declaration</em>}'.
   * <!-- begin-user-doc -->
   * This default implementation returns null so that we can easily ignore cases;
   * it's useful to ignore a case when inheritance will catch all the cases anyway.
   * <!-- end-user-doc -->
   * @return the new adapter.
   * @see org.deltaj.deltaj.LocalVariableDeclaration
   * @generated
   */
  public Adapter createLocalVariableDeclarationAdapter()
  {
    return null;
  }

  /**
   * Creates a new adapter for an object of class '{@link org.deltaj.deltaj.Parameter <em>Parameter</em>}'.
   * <!-- begin-user-doc -->
   * This default implementation returns null so that we can easily ignore cases;
   * it's useful to ignore a case when inheritance will catch all the cases anyway.
   * <!-- end-user-doc -->
   * @return the new adapter.
   * @see org.deltaj.deltaj.Parameter
   * @generated
   */
  public Adapter createParameterAdapter()
  {
    return null;
  }

  /**
   * Creates a new adapter for an object of class '{@link org.deltaj.deltaj.Method <em>Method</em>}'.
   * <!-- begin-user-doc -->
   * This default implementation returns null so that we can easily ignore cases;
   * it's useful to ignore a case when inheritance will catch all the cases anyway.
   * <!-- end-user-doc -->
   * @return the new adapter.
   * @see org.deltaj.deltaj.Method
   * @generated
   */
  public Adapter createMethodAdapter()
  {
    return null;
  }

  /**
   * Creates a new adapter for an object of class '{@link org.deltaj.deltaj.StatementBlock <em>Statement Block</em>}'.
   * <!-- begin-user-doc -->
   * This default implementation returns null so that we can easily ignore cases;
   * it's useful to ignore a case when inheritance will catch all the cases anyway.
   * <!-- end-user-doc -->
   * @return the new adapter.
   * @see org.deltaj.deltaj.StatementBlock
   * @generated
   */
  public Adapter createStatementBlockAdapter()
  {
    return null;
  }

  /**
   * Creates a new adapter for an object of class '{@link org.deltaj.deltaj.Statement <em>Statement</em>}'.
   * <!-- begin-user-doc -->
   * This default implementation returns null so that we can easily ignore cases;
   * it's useful to ignore a case when inheritance will catch all the cases anyway.
   * <!-- end-user-doc -->
   * @return the new adapter.
   * @see org.deltaj.deltaj.Statement
   * @generated
   */
  public Adapter createStatementAdapter()
  {
    return null;
  }

  /**
   * Creates a new adapter for an object of class '{@link org.deltaj.deltaj.ExpressionStatement <em>Expression Statement</em>}'.
   * <!-- begin-user-doc -->
   * This default implementation returns null so that we can easily ignore cases;
   * it's useful to ignore a case when inheritance will catch all the cases anyway.
   * <!-- end-user-doc -->
   * @return the new adapter.
   * @see org.deltaj.deltaj.ExpressionStatement
   * @generated
   */
  public Adapter createExpressionStatementAdapter()
  {
    return null;
  }

  /**
   * Creates a new adapter for an object of class '{@link org.deltaj.deltaj.Assignment <em>Assignment</em>}'.
   * <!-- begin-user-doc -->
   * This default implementation returns null so that we can easily ignore cases;
   * it's useful to ignore a case when inheritance will catch all the cases anyway.
   * <!-- end-user-doc -->
   * @return the new adapter.
   * @see org.deltaj.deltaj.Assignment
   * @generated
   */
  public Adapter createAssignmentAdapter()
  {
    return null;
  }

  /**
   * Creates a new adapter for an object of class '{@link org.deltaj.deltaj.IfStatement <em>If Statement</em>}'.
   * <!-- begin-user-doc -->
   * This default implementation returns null so that we can easily ignore cases;
   * it's useful to ignore a case when inheritance will catch all the cases anyway.
   * <!-- end-user-doc -->
   * @return the new adapter.
   * @see org.deltaj.deltaj.IfStatement
   * @generated
   */
  public Adapter createIfStatementAdapter()
  {
    return null;
  }

  /**
   * Creates a new adapter for an object of class '{@link org.deltaj.deltaj.Expression <em>Expression</em>}'.
   * <!-- begin-user-doc -->
   * This default implementation returns null so that we can easily ignore cases;
   * it's useful to ignore a case when inheritance will catch all the cases anyway.
   * <!-- end-user-doc -->
   * @return the new adapter.
   * @see org.deltaj.deltaj.Expression
   * @generated
   */
  public Adapter createExpressionAdapter()
  {
    return null;
  }

  /**
   * Creates a new adapter for an object of class '{@link org.deltaj.deltaj.Null <em>Null</em>}'.
   * <!-- begin-user-doc -->
   * This default implementation returns null so that we can easily ignore cases;
   * it's useful to ignore a case when inheritance will catch all the cases anyway.
   * <!-- end-user-doc -->
   * @return the new adapter.
   * @see org.deltaj.deltaj.Null
   * @generated
   */
  public Adapter createNullAdapter()
  {
    return null;
  }

  /**
   * Creates a new adapter for an object of class '{@link org.deltaj.deltaj.This <em>This</em>}'.
   * <!-- begin-user-doc -->
   * This default implementation returns null so that we can easily ignore cases;
   * it's useful to ignore a case when inheritance will catch all the cases anyway.
   * <!-- end-user-doc -->
   * @return the new adapter.
   * @see org.deltaj.deltaj.This
   * @generated
   */
  public Adapter createThisAdapter()
  {
    return null;
  }

  /**
   * Creates a new adapter for an object of class '{@link org.deltaj.deltaj.Original <em>Original</em>}'.
   * <!-- begin-user-doc -->
   * This default implementation returns null so that we can easily ignore cases;
   * it's useful to ignore a case when inheritance will catch all the cases anyway.
   * <!-- end-user-doc -->
   * @return the new adapter.
   * @see org.deltaj.deltaj.Original
   * @generated
   */
  public Adapter createOriginalAdapter()
  {
    return null;
  }

  /**
   * Creates a new adapter for an object of class '{@link org.deltaj.deltaj.VariableAccess <em>Variable Access</em>}'.
   * <!-- begin-user-doc -->
   * This default implementation returns null so that we can easily ignore cases;
   * it's useful to ignore a case when inheritance will catch all the cases anyway.
   * <!-- end-user-doc -->
   * @return the new adapter.
   * @see org.deltaj.deltaj.VariableAccess
   * @generated
   */
  public Adapter createVariableAccessAdapter()
  {
    return null;
  }

  /**
   * Creates a new adapter for an object of class '{@link org.deltaj.deltaj.New <em>New</em>}'.
   * <!-- begin-user-doc -->
   * This default implementation returns null so that we can easily ignore cases;
   * it's useful to ignore a case when inheritance will catch all the cases anyway.
   * <!-- end-user-doc -->
   * @return the new adapter.
   * @see org.deltaj.deltaj.New
   * @generated
   */
  public Adapter createNewAdapter()
  {
    return null;
  }

  /**
   * Creates a new adapter for an object of class '{@link org.deltaj.deltaj.Cast <em>Cast</em>}'.
   * <!-- begin-user-doc -->
   * This default implementation returns null so that we can easily ignore cases;
   * it's useful to ignore a case when inheritance will catch all the cases anyway.
   * <!-- end-user-doc -->
   * @return the new adapter.
   * @see org.deltaj.deltaj.Cast
   * @generated
   */
  public Adapter createCastAdapter()
  {
    return null;
  }

  /**
   * Creates a new adapter for an object of class '{@link org.deltaj.deltaj.Paren <em>Paren</em>}'.
   * <!-- begin-user-doc -->
   * This default implementation returns null so that we can easily ignore cases;
   * it's useful to ignore a case when inheritance will catch all the cases anyway.
   * <!-- end-user-doc -->
   * @return the new adapter.
   * @see org.deltaj.deltaj.Paren
   * @generated
   */
  public Adapter createParenAdapter()
  {
    return null;
  }

  /**
   * Creates a new adapter for an object of class '{@link org.deltaj.deltaj.Constant <em>Constant</em>}'.
   * <!-- begin-user-doc -->
   * This default implementation returns null so that we can easily ignore cases;
   * it's useful to ignore a case when inheritance will catch all the cases anyway.
   * <!-- end-user-doc -->
   * @return the new adapter.
   * @see org.deltaj.deltaj.Constant
   * @generated
   */
  public Adapter createConstantAdapter()
  {
    return null;
  }

  /**
   * Creates a new adapter for an object of class '{@link org.deltaj.deltaj.StringConstant <em>String Constant</em>}'.
   * <!-- begin-user-doc -->
   * This default implementation returns null so that we can easily ignore cases;
   * it's useful to ignore a case when inheritance will catch all the cases anyway.
   * <!-- end-user-doc -->
   * @return the new adapter.
   * @see org.deltaj.deltaj.StringConstant
   * @generated
   */
  public Adapter createStringConstantAdapter()
  {
    return null;
  }

  /**
   * Creates a new adapter for an object of class '{@link org.deltaj.deltaj.IntConstant <em>Int Constant</em>}'.
   * <!-- begin-user-doc -->
   * This default implementation returns null so that we can easily ignore cases;
   * it's useful to ignore a case when inheritance will catch all the cases anyway.
   * <!-- end-user-doc -->
   * @return the new adapter.
   * @see org.deltaj.deltaj.IntConstant
   * @generated
   */
  public Adapter createIntConstantAdapter()
  {
    return null;
  }

  /**
   * Creates a new adapter for an object of class '{@link org.deltaj.deltaj.BoolConstant <em>Bool Constant</em>}'.
   * <!-- begin-user-doc -->
   * This default implementation returns null so that we can easily ignore cases;
   * it's useful to ignore a case when inheritance will catch all the cases anyway.
   * <!-- end-user-doc -->
   * @return the new adapter.
   * @see org.deltaj.deltaj.BoolConstant
   * @generated
   */
  public Adapter createBoolConstantAdapter()
  {
    return null;
  }

  /**
   * Creates a new adapter for an object of class '{@link org.deltaj.deltaj.Message <em>Message</em>}'.
   * <!-- begin-user-doc -->
   * This default implementation returns null so that we can easily ignore cases;
   * it's useful to ignore a case when inheritance will catch all the cases anyway.
   * <!-- end-user-doc -->
   * @return the new adapter.
   * @see org.deltaj.deltaj.Message
   * @generated
   */
  public Adapter createMessageAdapter()
  {
    return null;
  }

  /**
   * Creates a new adapter for an object of class '{@link org.deltaj.deltaj.MethodCall <em>Method Call</em>}'.
   * <!-- begin-user-doc -->
   * This default implementation returns null so that we can easily ignore cases;
   * it's useful to ignore a case when inheritance will catch all the cases anyway.
   * <!-- end-user-doc -->
   * @return the new adapter.
   * @see org.deltaj.deltaj.MethodCall
   * @generated
   */
  public Adapter createMethodCallAdapter()
  {
    return null;
  }

  /**
   * Creates a new adapter for an object of class '{@link org.deltaj.deltaj.FieldSelection <em>Field Selection</em>}'.
   * <!-- begin-user-doc -->
   * This default implementation returns null so that we can easily ignore cases;
   * it's useful to ignore a case when inheritance will catch all the cases anyway.
   * <!-- end-user-doc -->
   * @return the new adapter.
   * @see org.deltaj.deltaj.FieldSelection
   * @generated
   */
  public Adapter createFieldSelectionAdapter()
  {
    return null;
  }

  /**
   * Creates a new adapter for an object of class '{@link org.deltaj.deltaj.DeltaModule <em>Delta Module</em>}'.
   * <!-- begin-user-doc -->
   * This default implementation returns null so that we can easily ignore cases;
   * it's useful to ignore a case when inheritance will catch all the cases anyway.
   * <!-- end-user-doc -->
   * @return the new adapter.
   * @see org.deltaj.deltaj.DeltaModule
   * @generated
   */
  public Adapter createDeltaModuleAdapter()
  {
    return null;
  }

  /**
   * Creates a new adapter for an object of class '{@link org.deltaj.deltaj.DeltaAction <em>Delta Action</em>}'.
   * <!-- begin-user-doc -->
   * This default implementation returns null so that we can easily ignore cases;
   * it's useful to ignore a case when inheritance will catch all the cases anyway.
   * <!-- end-user-doc -->
   * @return the new adapter.
   * @see org.deltaj.deltaj.DeltaAction
   * @generated
   */
  public Adapter createDeltaActionAdapter()
  {
    return null;
  }

  /**
   * Creates a new adapter for an object of class '{@link org.deltaj.deltaj.ClassAddition <em>Class Addition</em>}'.
   * <!-- begin-user-doc -->
   * This default implementation returns null so that we can easily ignore cases;
   * it's useful to ignore a case when inheritance will catch all the cases anyway.
   * <!-- end-user-doc -->
   * @return the new adapter.
   * @see org.deltaj.deltaj.ClassAddition
   * @generated
   */
  public Adapter createClassAdditionAdapter()
  {
    return null;
  }

  /**
   * Creates a new adapter for an object of class '{@link org.deltaj.deltaj.RemovesOrModifiesClass <em>Removes Or Modifies Class</em>}'.
   * <!-- begin-user-doc -->
   * This default implementation returns null so that we can easily ignore cases;
   * it's useful to ignore a case when inheritance will catch all the cases anyway.
   * <!-- end-user-doc -->
   * @return the new adapter.
   * @see org.deltaj.deltaj.RemovesOrModifiesClass
   * @generated
   */
  public Adapter createRemovesOrModifiesClassAdapter()
  {
    return null;
  }

  /**
   * Creates a new adapter for an object of class '{@link org.deltaj.deltaj.ClassRemoval <em>Class Removal</em>}'.
   * <!-- begin-user-doc -->
   * This default implementation returns null so that we can easily ignore cases;
   * it's useful to ignore a case when inheritance will catch all the cases anyway.
   * <!-- end-user-doc -->
   * @return the new adapter.
   * @see org.deltaj.deltaj.ClassRemoval
   * @generated
   */
  public Adapter createClassRemovalAdapter()
  {
    return null;
  }

  /**
   * Creates a new adapter for an object of class '{@link org.deltaj.deltaj.ClassModification <em>Class Modification</em>}'.
   * <!-- begin-user-doc -->
   * This default implementation returns null so that we can easily ignore cases;
   * it's useful to ignore a case when inheritance will catch all the cases anyway.
   * <!-- end-user-doc -->
   * @return the new adapter.
   * @see org.deltaj.deltaj.ClassModification
   * @generated
   */
  public Adapter createClassModificationAdapter()
  {
    return null;
  }

  /**
   * Creates a new adapter for an object of class '{@link org.deltaj.deltaj.DeltaSubAction <em>Delta Sub Action</em>}'.
   * <!-- begin-user-doc -->
   * This default implementation returns null so that we can easily ignore cases;
   * it's useful to ignore a case when inheritance will catch all the cases anyway.
   * <!-- end-user-doc -->
   * @return the new adapter.
   * @see org.deltaj.deltaj.DeltaSubAction
   * @generated
   */
  public Adapter createDeltaSubActionAdapter()
  {
    return null;
  }

  /**
   * Creates a new adapter for an object of class '{@link org.deltaj.deltaj.MethodOrFieldAddition <em>Method Or Field Addition</em>}'.
   * <!-- begin-user-doc -->
   * This default implementation returns null so that we can easily ignore cases;
   * it's useful to ignore a case when inheritance will catch all the cases anyway.
   * <!-- end-user-doc -->
   * @return the new adapter.
   * @see org.deltaj.deltaj.MethodOrFieldAddition
   * @generated
   */
  public Adapter createMethodOrFieldAdditionAdapter()
  {
    return null;
  }

  /**
   * Creates a new adapter for an object of class '{@link org.deltaj.deltaj.FieldAddition <em>Field Addition</em>}'.
   * <!-- begin-user-doc -->
   * This default implementation returns null so that we can easily ignore cases;
   * it's useful to ignore a case when inheritance will catch all the cases anyway.
   * <!-- end-user-doc -->
   * @return the new adapter.
   * @see org.deltaj.deltaj.FieldAddition
   * @generated
   */
  public Adapter createFieldAdditionAdapter()
  {
    return null;
  }

  /**
   * Creates a new adapter for an object of class '{@link org.deltaj.deltaj.MethodAddition <em>Method Addition</em>}'.
   * <!-- begin-user-doc -->
   * This default implementation returns null so that we can easily ignore cases;
   * it's useful to ignore a case when inheritance will catch all the cases anyway.
   * <!-- end-user-doc -->
   * @return the new adapter.
   * @see org.deltaj.deltaj.MethodAddition
   * @generated
   */
  public Adapter createMethodAdditionAdapter()
  {
    return null;
  }

  /**
   * Creates a new adapter for an object of class '{@link org.deltaj.deltaj.FieldRemoval <em>Field Removal</em>}'.
   * <!-- begin-user-doc -->
   * This default implementation returns null so that we can easily ignore cases;
   * it's useful to ignore a case when inheritance will catch all the cases anyway.
   * <!-- end-user-doc -->
   * @return the new adapter.
   * @see org.deltaj.deltaj.FieldRemoval
   * @generated
   */
  public Adapter createFieldRemovalAdapter()
  {
    return null;
  }

  /**
   * Creates a new adapter for an object of class '{@link org.deltaj.deltaj.MethodRemoval <em>Method Removal</em>}'.
   * <!-- begin-user-doc -->
   * This default implementation returns null so that we can easily ignore cases;
   * it's useful to ignore a case when inheritance will catch all the cases anyway.
   * <!-- end-user-doc -->
   * @return the new adapter.
   * @see org.deltaj.deltaj.MethodRemoval
   * @generated
   */
  public Adapter createMethodRemovalAdapter()
  {
    return null;
  }

  /**
   * Creates a new adapter for an object of class '{@link org.deltaj.deltaj.MethodModification <em>Method Modification</em>}'.
   * <!-- begin-user-doc -->
   * This default implementation returns null so that we can easily ignore cases;
   * it's useful to ignore a case when inheritance will catch all the cases anyway.
   * <!-- end-user-doc -->
   * @return the new adapter.
   * @see org.deltaj.deltaj.MethodModification
   * @generated
   */
  public Adapter createMethodModificationAdapter()
  {
    return null;
  }

  /**
   * Creates a new adapter for an object of class '{@link org.deltaj.deltaj.ProductLine <em>Product Line</em>}'.
   * <!-- begin-user-doc -->
   * This default implementation returns null so that we can easily ignore cases;
   * it's useful to ignore a case when inheritance will catch all the cases anyway.
   * <!-- end-user-doc -->
   * @return the new adapter.
   * @see org.deltaj.deltaj.ProductLine
   * @generated
   */
  public Adapter createProductLineAdapter()
  {
    return null;
  }

  /**
   * Creates a new adapter for an object of class '{@link org.deltaj.deltaj.Features <em>Features</em>}'.
   * <!-- begin-user-doc -->
   * This default implementation returns null so that we can easily ignore cases;
   * it's useful to ignore a case when inheritance will catch all the cases anyway.
   * <!-- end-user-doc -->
   * @return the new adapter.
   * @see org.deltaj.deltaj.Features
   * @generated
   */
  public Adapter createFeaturesAdapter()
  {
    return null;
  }

  /**
   * Creates a new adapter for an object of class '{@link org.deltaj.deltaj.Feature <em>Feature</em>}'.
   * <!-- begin-user-doc -->
   * This default implementation returns null so that we can easily ignore cases;
   * it's useful to ignore a case when inheritance will catch all the cases anyway.
   * <!-- end-user-doc -->
   * @return the new adapter.
   * @see org.deltaj.deltaj.Feature
   * @generated
   */
  public Adapter createFeatureAdapter()
  {
    return null;
  }

  /**
   * Creates a new adapter for an object of class '{@link org.deltaj.deltaj.Configurations <em>Configurations</em>}'.
   * <!-- begin-user-doc -->
   * This default implementation returns null so that we can easily ignore cases;
   * it's useful to ignore a case when inheritance will catch all the cases anyway.
   * <!-- end-user-doc -->
   * @return the new adapter.
   * @see org.deltaj.deltaj.Configurations
   * @generated
   */
  public Adapter createConfigurationsAdapter()
  {
    return null;
  }

  /**
   * Creates a new adapter for an object of class '{@link org.deltaj.deltaj.Configuration <em>Configuration</em>}'.
   * <!-- begin-user-doc -->
   * This default implementation returns null so that we can easily ignore cases;
   * it's useful to ignore a case when inheritance will catch all the cases anyway.
   * <!-- end-user-doc -->
   * @return the new adapter.
   * @see org.deltaj.deltaj.Configuration
   * @generated
   */
  public Adapter createConfigurationAdapter()
  {
    return null;
  }

  /**
   * Creates a new adapter for an object of class '{@link org.deltaj.deltaj.DeltaPartition <em>Delta Partition</em>}'.
   * <!-- begin-user-doc -->
   * This default implementation returns null so that we can easily ignore cases;
   * it's useful to ignore a case when inheritance will catch all the cases anyway.
   * <!-- end-user-doc -->
   * @return the new adapter.
   * @see org.deltaj.deltaj.DeltaPartition
   * @generated
   */
  public Adapter createDeltaPartitionAdapter()
  {
    return null;
  }

  /**
   * Creates a new adapter for an object of class '{@link org.deltaj.deltaj.PartitionPart <em>Partition Part</em>}'.
   * <!-- begin-user-doc -->
   * This default implementation returns null so that we can easily ignore cases;
   * it's useful to ignore a case when inheritance will catch all the cases anyway.
   * <!-- end-user-doc -->
   * @return the new adapter.
   * @see org.deltaj.deltaj.PartitionPart
   * @generated
   */
  public Adapter createPartitionPartAdapter()
  {
    return null;
  }

  /**
   * Creates a new adapter for an object of class '{@link org.deltaj.deltaj.ModuleReference <em>Module Reference</em>}'.
   * <!-- begin-user-doc -->
   * This default implementation returns null so that we can easily ignore cases;
   * it's useful to ignore a case when inheritance will catch all the cases anyway.
   * <!-- end-user-doc -->
   * @return the new adapter.
   * @see org.deltaj.deltaj.ModuleReference
   * @generated
   */
  public Adapter createModuleReferenceAdapter()
  {
    return null;
  }

  /**
   * Creates a new adapter for an object of class '{@link org.deltaj.deltaj.PropositionalFormula <em>Propositional Formula</em>}'.
   * <!-- begin-user-doc -->
   * This default implementation returns null so that we can easily ignore cases;
   * it's useful to ignore a case when inheritance will catch all the cases anyway.
   * <!-- end-user-doc -->
   * @return the new adapter.
   * @see org.deltaj.deltaj.PropositionalFormula
   * @generated
   */
  public Adapter createPropositionalFormulaAdapter()
  {
    return null;
  }

  /**
   * Creates a new adapter for an object of class '{@link org.deltaj.deltaj.Product <em>Product</em>}'.
   * <!-- begin-user-doc -->
   * This default implementation returns null so that we can easily ignore cases;
   * it's useful to ignore a case when inheritance will catch all the cases anyway.
   * <!-- end-user-doc -->
   * @return the new adapter.
   * @see org.deltaj.deltaj.Product
   * @generated
   */
  public Adapter createProductAdapter()
  {
    return null;
  }

  /**
   * Creates a new adapter for an object of class '{@link org.deltaj.deltaj.ReturnStatement <em>Return Statement</em>}'.
   * <!-- begin-user-doc -->
   * This default implementation returns null so that we can easily ignore cases;
   * it's useful to ignore a case when inheritance will catch all the cases anyway.
   * <!-- end-user-doc -->
   * @return the new adapter.
   * @see org.deltaj.deltaj.ReturnStatement
   * @generated
   */
  public Adapter createReturnStatementAdapter()
  {
    return null;
  }

  /**
   * Creates a new adapter for an object of class '{@link org.deltaj.deltaj.JavaVerbatim <em>Java Verbatim</em>}'.
   * <!-- begin-user-doc -->
   * This default implementation returns null so that we can easily ignore cases;
   * it's useful to ignore a case when inheritance will catch all the cases anyway.
   * <!-- end-user-doc -->
   * @return the new adapter.
   * @see org.deltaj.deltaj.JavaVerbatim
   * @generated
   */
  public Adapter createJavaVerbatimAdapter()
  {
    return null;
  }

  /**
   * Creates a new adapter for an object of class '{@link org.deltaj.deltaj.Plus <em>Plus</em>}'.
   * <!-- begin-user-doc -->
   * This default implementation returns null so that we can easily ignore cases;
   * it's useful to ignore a case when inheritance will catch all the cases anyway.
   * <!-- end-user-doc -->
   * @return the new adapter.
   * @see org.deltaj.deltaj.Plus
   * @generated
   */
  public Adapter createPlusAdapter()
  {
    return null;
  }

  /**
   * Creates a new adapter for an object of class '{@link org.deltaj.deltaj.Minus <em>Minus</em>}'.
   * <!-- begin-user-doc -->
   * This default implementation returns null so that we can easily ignore cases;
   * it's useful to ignore a case when inheritance will catch all the cases anyway.
   * <!-- end-user-doc -->
   * @return the new adapter.
   * @see org.deltaj.deltaj.Minus
   * @generated
   */
  public Adapter createMinusAdapter()
  {
    return null;
  }

  /**
   * Creates a new adapter for an object of class '{@link org.deltaj.deltaj.MultiOrDiv <em>Multi Or Div</em>}'.
   * <!-- begin-user-doc -->
   * This default implementation returns null so that we can easily ignore cases;
   * it's useful to ignore a case when inheritance will catch all the cases anyway.
   * <!-- end-user-doc -->
   * @return the new adapter.
   * @see org.deltaj.deltaj.MultiOrDiv
   * @generated
   */
  public Adapter createMultiOrDivAdapter()
  {
    return null;
  }

  /**
   * Creates a new adapter for an object of class '{@link org.deltaj.deltaj.Comparison <em>Comparison</em>}'.
   * <!-- begin-user-doc -->
   * This default implementation returns null so that we can easily ignore cases;
   * it's useful to ignore a case when inheritance will catch all the cases anyway.
   * <!-- end-user-doc -->
   * @return the new adapter.
   * @see org.deltaj.deltaj.Comparison
   * @generated
   */
  public Adapter createComparisonAdapter()
  {
    return null;
  }

  /**
   * Creates a new adapter for an object of class '{@link org.deltaj.deltaj.AndOrExpression <em>And Or Expression</em>}'.
   * <!-- begin-user-doc -->
   * This default implementation returns null so that we can easily ignore cases;
   * it's useful to ignore a case when inheritance will catch all the cases anyway.
   * <!-- end-user-doc -->
   * @return the new adapter.
   * @see org.deltaj.deltaj.AndOrExpression
   * @generated
   */
  public Adapter createAndOrExpressionAdapter()
  {
    return null;
  }

  /**
   * Creates a new adapter for an object of class '{@link org.deltaj.deltaj.BooleanNegation <em>Boolean Negation</em>}'.
   * <!-- begin-user-doc -->
   * This default implementation returns null so that we can easily ignore cases;
   * it's useful to ignore a case when inheritance will catch all the cases anyway.
   * <!-- end-user-doc -->
   * @return the new adapter.
   * @see org.deltaj.deltaj.BooleanNegation
   * @generated
   */
  public Adapter createBooleanNegationAdapter()
  {
    return null;
  }

  /**
   * Creates a new adapter for an object of class '{@link org.deltaj.deltaj.ArithmeticSigned <em>Arithmetic Signed</em>}'.
   * <!-- begin-user-doc -->
   * This default implementation returns null so that we can easily ignore cases;
   * it's useful to ignore a case when inheritance will catch all the cases anyway.
   * <!-- end-user-doc -->
   * @return the new adapter.
   * @see org.deltaj.deltaj.ArithmeticSigned
   * @generated
   */
  public Adapter createArithmeticSignedAdapter()
  {
    return null;
  }

  /**
   * Creates a new adapter for an object of class '{@link org.deltaj.deltaj.Selection <em>Selection</em>}'.
   * <!-- begin-user-doc -->
   * This default implementation returns null so that we can easily ignore cases;
   * it's useful to ignore a case when inheritance will catch all the cases anyway.
   * <!-- end-user-doc -->
   * @return the new adapter.
   * @see org.deltaj.deltaj.Selection
   * @generated
   */
  public Adapter createSelectionAdapter()
  {
    return null;
  }

  /**
   * Creates a new adapter for an object of class '{@link org.deltaj.deltaj.Or <em>Or</em>}'.
   * <!-- begin-user-doc -->
   * This default implementation returns null so that we can easily ignore cases;
   * it's useful to ignore a case when inheritance will catch all the cases anyway.
   * <!-- end-user-doc -->
   * @return the new adapter.
   * @see org.deltaj.deltaj.Or
   * @generated
   */
  public Adapter createOrAdapter()
  {
    return null;
  }

  /**
   * Creates a new adapter for an object of class '{@link org.deltaj.deltaj.And <em>And</em>}'.
   * <!-- begin-user-doc -->
   * This default implementation returns null so that we can easily ignore cases;
   * it's useful to ignore a case when inheritance will catch all the cases anyway.
   * <!-- end-user-doc -->
   * @return the new adapter.
   * @see org.deltaj.deltaj.And
   * @generated
   */
  public Adapter createAndAdapter()
  {
    return null;
  }

  /**
   * Creates a new adapter for an object of class '{@link org.deltaj.deltaj.FeatureRef <em>Feature Ref</em>}'.
   * <!-- begin-user-doc -->
   * This default implementation returns null so that we can easily ignore cases;
   * it's useful to ignore a case when inheritance will catch all the cases anyway.
   * <!-- end-user-doc -->
   * @return the new adapter.
   * @see org.deltaj.deltaj.FeatureRef
   * @generated
   */
  public Adapter createFeatureRefAdapter()
  {
    return null;
  }

  /**
   * Creates a new adapter for an object of class '{@link org.deltaj.deltaj.PropParen <em>Prop Paren</em>}'.
   * <!-- begin-user-doc -->
   * This default implementation returns null so that we can easily ignore cases;
   * it's useful to ignore a case when inheritance will catch all the cases anyway.
   * <!-- end-user-doc -->
   * @return the new adapter.
   * @see org.deltaj.deltaj.PropParen
   * @generated
   */
  public Adapter createPropParenAdapter()
  {
    return null;
  }

  /**
   * Creates a new adapter for an object of class '{@link org.deltaj.deltaj.Negation <em>Negation</em>}'.
   * <!-- begin-user-doc -->
   * This default implementation returns null so that we can easily ignore cases;
   * it's useful to ignore a case when inheritance will catch all the cases anyway.
   * <!-- end-user-doc -->
   * @return the new adapter.
   * @see org.deltaj.deltaj.Negation
   * @generated
   */
  public Adapter createNegationAdapter()
  {
    return null;
  }

  /**
   * Creates a new adapter for an object of class '{@link org.deltaj.deltaj.PropTrue <em>Prop True</em>}'.
   * <!-- begin-user-doc -->
   * This default implementation returns null so that we can easily ignore cases;
   * it's useful to ignore a case when inheritance will catch all the cases anyway.
   * <!-- end-user-doc -->
   * @return the new adapter.
   * @see org.deltaj.deltaj.PropTrue
   * @generated
   */
  public Adapter createPropTrueAdapter()
  {
    return null;
  }

  /**
   * Creates a new adapter for an object of class '{@link org.deltaj.deltaj.PropFalse <em>Prop False</em>}'.
   * <!-- begin-user-doc -->
   * This default implementation returns null so that we can easily ignore cases;
   * it's useful to ignore a case when inheritance will catch all the cases anyway.
   * <!-- end-user-doc -->
   * @return the new adapter.
   * @see org.deltaj.deltaj.PropFalse
   * @generated
   */
  public Adapter createPropFalseAdapter()
  {
    return null;
  }

  /**
   * Creates a new adapter for the default case.
   * <!-- begin-user-doc -->
   * This default implementation returns null.
   * <!-- end-user-doc -->
   * @return the new adapter.
   * @generated
   */
  public Adapter createEObjectAdapter()
  {
    return null;
  }

} //DeltajAdapterFactory
