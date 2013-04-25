/**
 * <copyright>
 * </copyright>
 *
 */
package org.deltaj.deltaj.impl;

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
import org.deltaj.deltaj.DeltajFactory;
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

import org.eclipse.emf.ecore.EClass;
import org.eclipse.emf.ecore.EObject;
import org.eclipse.emf.ecore.EPackage;

import org.eclipse.emf.ecore.impl.EFactoryImpl;

import org.eclipse.emf.ecore.plugin.EcorePlugin;

/**
 * <!-- begin-user-doc -->
 * An implementation of the model <b>Factory</b>.
 * <!-- end-user-doc -->
 * @generated
 */
public class DeltajFactoryImpl extends EFactoryImpl implements DeltajFactory
{
  /**
   * Creates the default factory implementation.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public static DeltajFactory init()
  {
    try
    {
      DeltajFactory theDeltajFactory = (DeltajFactory)EPackage.Registry.INSTANCE.getEFactory("http://www.deltaj.org/DeltaJ"); 
      if (theDeltajFactory != null)
      {
        return theDeltajFactory;
      }
    }
    catch (Exception exception)
    {
      EcorePlugin.INSTANCE.log(exception);
    }
    return new DeltajFactoryImpl();
  }

  /**
   * Creates an instance of the factory.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public DeltajFactoryImpl()
  {
    super();
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  @Override
  public EObject create(EClass eClass)
  {
    switch (eClass.getClassifierID())
    {
      case DeltajPackage.PROGRAM: return createProgram();
      case DeltajPackage.TYPE: return createType();
      case DeltajPackage.TYPE_VARIABLE: return createTypeVariable();
      case DeltajPackage.TYPE_FOR_METHOD: return createTypeForMethod();
      case DeltajPackage.VOID_TYPE: return createVoidType();
      case DeltajPackage.TYPE_FOR_DECLARATION: return createTypeForDeclaration();
      case DeltajPackage.BASIC_TYPE: return createBasicType();
      case DeltajPackage.INT_TYPE: return createIntType();
      case DeltajPackage.BOOLEAN_TYPE: return createBooleanType();
      case DeltajPackage.STRING_TYPE: return createStringType();
      case DeltajPackage.CLASS_TYPE: return createClassType();
      case DeltajPackage.CLASS: return createClass();
      case DeltajPackage.TYPED_DECLARATION: return createTypedDeclaration();
      case DeltajPackage.FIELD: return createField();
      case DeltajPackage.LOCAL_VARIABLE_DECLARATION: return createLocalVariableDeclaration();
      case DeltajPackage.PARAMETER: return createParameter();
      case DeltajPackage.METHOD: return createMethod();
      case DeltajPackage.STATEMENT_BLOCK: return createStatementBlock();
      case DeltajPackage.STATEMENT: return createStatement();
      case DeltajPackage.EXPRESSION_STATEMENT: return createExpressionStatement();
      case DeltajPackage.ASSIGNMENT: return createAssignment();
      case DeltajPackage.IF_STATEMENT: return createIfStatement();
      case DeltajPackage.EXPRESSION: return createExpression();
      case DeltajPackage.NULL: return createNull();
      case DeltajPackage.THIS: return createThis();
      case DeltajPackage.ORIGINAL: return createOriginal();
      case DeltajPackage.VARIABLE_ACCESS: return createVariableAccess();
      case DeltajPackage.NEW: return createNew();
      case DeltajPackage.CAST: return createCast();
      case DeltajPackage.PAREN: return createParen();
      case DeltajPackage.CONSTANT: return createConstant();
      case DeltajPackage.STRING_CONSTANT: return createStringConstant();
      case DeltajPackage.INT_CONSTANT: return createIntConstant();
      case DeltajPackage.BOOL_CONSTANT: return createBoolConstant();
      case DeltajPackage.MESSAGE: return createMessage();
      case DeltajPackage.METHOD_CALL: return createMethodCall();
      case DeltajPackage.FIELD_SELECTION: return createFieldSelection();
      case DeltajPackage.DELTA_MODULE: return createDeltaModule();
      case DeltajPackage.DELTA_ACTION: return createDeltaAction();
      case DeltajPackage.CLASS_ADDITION: return createClassAddition();
      case DeltajPackage.REMOVES_OR_MODIFIES_CLASS: return createRemovesOrModifiesClass();
      case DeltajPackage.CLASS_REMOVAL: return createClassRemoval();
      case DeltajPackage.CLASS_MODIFICATION: return createClassModification();
      case DeltajPackage.DELTA_SUB_ACTION: return createDeltaSubAction();
      case DeltajPackage.METHOD_OR_FIELD_ADDITION: return createMethodOrFieldAddition();
      case DeltajPackage.FIELD_ADDITION: return createFieldAddition();
      case DeltajPackage.METHOD_ADDITION: return createMethodAddition();
      case DeltajPackage.FIELD_REMOVAL: return createFieldRemoval();
      case DeltajPackage.METHOD_REMOVAL: return createMethodRemoval();
      case DeltajPackage.METHOD_MODIFICATION: return createMethodModification();
      case DeltajPackage.PRODUCT_LINE: return createProductLine();
      case DeltajPackage.FEATURES: return createFeatures();
      case DeltajPackage.FEATURE: return createFeature();
      case DeltajPackage.CONFIGURATIONS: return createConfigurations();
      case DeltajPackage.CONFIGURATION: return createConfiguration();
      case DeltajPackage.DELTA_PARTITION: return createDeltaPartition();
      case DeltajPackage.PARTITION_PART: return createPartitionPart();
      case DeltajPackage.MODULE_REFERENCE: return createModuleReference();
      case DeltajPackage.PROPOSITIONAL_FORMULA: return createPropositionalFormula();
      case DeltajPackage.PRODUCT: return createProduct();
      case DeltajPackage.RETURN_STATEMENT: return createReturnStatement();
      case DeltajPackage.JAVA_VERBATIM: return createJavaVerbatim();
      case DeltajPackage.PLUS: return createPlus();
      case DeltajPackage.MINUS: return createMinus();
      case DeltajPackage.MULTI_OR_DIV: return createMultiOrDiv();
      case DeltajPackage.COMPARISON: return createComparison();
      case DeltajPackage.AND_OR_EXPRESSION: return createAndOrExpression();
      case DeltajPackage.BOOLEAN_NEGATION: return createBooleanNegation();
      case DeltajPackage.ARITHMETIC_SIGNED: return createArithmeticSigned();
      case DeltajPackage.SELECTION: return createSelection();
      case DeltajPackage.OR: return createOr();
      case DeltajPackage.AND: return createAnd();
      case DeltajPackage.FEATURE_REF: return createFeatureRef();
      case DeltajPackage.PROP_PAREN: return createPropParen();
      case DeltajPackage.NEGATION: return createNegation();
      case DeltajPackage.PROP_TRUE: return createPropTrue();
      case DeltajPackage.PROP_FALSE: return createPropFalse();
      default:
        throw new IllegalArgumentException("The class '" + eClass.getName() + "' is not a valid classifier");
    }
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public Program createProgram()
  {
    ProgramImpl program = new ProgramImpl();
    return program;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public Type createType()
  {
    TypeImpl type = new TypeImpl();
    return type;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public TypeVariable createTypeVariable()
  {
    TypeVariableImpl typeVariable = new TypeVariableImpl();
    return typeVariable;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public TypeForMethod createTypeForMethod()
  {
    TypeForMethodImpl typeForMethod = new TypeForMethodImpl();
    return typeForMethod;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public VoidType createVoidType()
  {
    VoidTypeImpl voidType = new VoidTypeImpl();
    return voidType;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public TypeForDeclaration createTypeForDeclaration()
  {
    TypeForDeclarationImpl typeForDeclaration = new TypeForDeclarationImpl();
    return typeForDeclaration;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public BasicType createBasicType()
  {
    BasicTypeImpl basicType = new BasicTypeImpl();
    return basicType;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public IntType createIntType()
  {
    IntTypeImpl intType = new IntTypeImpl();
    return intType;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public BooleanType createBooleanType()
  {
    BooleanTypeImpl booleanType = new BooleanTypeImpl();
    return booleanType;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public StringType createStringType()
  {
    StringTypeImpl stringType = new StringTypeImpl();
    return stringType;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public ClassType createClassType()
  {
    ClassTypeImpl classType = new ClassTypeImpl();
    return classType;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public org.deltaj.deltaj.Class createClass()
  {
    ClassImpl class_ = new ClassImpl();
    return class_;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public TypedDeclaration createTypedDeclaration()
  {
    TypedDeclarationImpl typedDeclaration = new TypedDeclarationImpl();
    return typedDeclaration;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public Field createField()
  {
    FieldImpl field = new FieldImpl();
    return field;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public LocalVariableDeclaration createLocalVariableDeclaration()
  {
    LocalVariableDeclarationImpl localVariableDeclaration = new LocalVariableDeclarationImpl();
    return localVariableDeclaration;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public Parameter createParameter()
  {
    ParameterImpl parameter = new ParameterImpl();
    return parameter;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public Method createMethod()
  {
    MethodImpl method = new MethodImpl();
    return method;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public StatementBlock createStatementBlock()
  {
    StatementBlockImpl statementBlock = new StatementBlockImpl();
    return statementBlock;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public Statement createStatement()
  {
    StatementImpl statement = new StatementImpl();
    return statement;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public ExpressionStatement createExpressionStatement()
  {
    ExpressionStatementImpl expressionStatement = new ExpressionStatementImpl();
    return expressionStatement;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public Assignment createAssignment()
  {
    AssignmentImpl assignment = new AssignmentImpl();
    return assignment;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public IfStatement createIfStatement()
  {
    IfStatementImpl ifStatement = new IfStatementImpl();
    return ifStatement;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public Expression createExpression()
  {
    ExpressionImpl expression = new ExpressionImpl();
    return expression;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public Null createNull()
  {
    NullImpl null_ = new NullImpl();
    return null_;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public This createThis()
  {
    ThisImpl this_ = new ThisImpl();
    return this_;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public Original createOriginal()
  {
    OriginalImpl original = new OriginalImpl();
    return original;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public VariableAccess createVariableAccess()
  {
    VariableAccessImpl variableAccess = new VariableAccessImpl();
    return variableAccess;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public New createNew()
  {
    NewImpl new_ = new NewImpl();
    return new_;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public Cast createCast()
  {
    CastImpl cast = new CastImpl();
    return cast;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public Paren createParen()
  {
    ParenImpl paren = new ParenImpl();
    return paren;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public Constant createConstant()
  {
    ConstantImpl constant = new ConstantImpl();
    return constant;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public StringConstant createStringConstant()
  {
    StringConstantImpl stringConstant = new StringConstantImpl();
    return stringConstant;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public IntConstant createIntConstant()
  {
    IntConstantImpl intConstant = new IntConstantImpl();
    return intConstant;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public BoolConstant createBoolConstant()
  {
    BoolConstantImpl boolConstant = new BoolConstantImpl();
    return boolConstant;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public Message createMessage()
  {
    MessageImpl message = new MessageImpl();
    return message;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public MethodCall createMethodCall()
  {
    MethodCallImpl methodCall = new MethodCallImpl();
    return methodCall;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public FieldSelection createFieldSelection()
  {
    FieldSelectionImpl fieldSelection = new FieldSelectionImpl();
    return fieldSelection;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public DeltaModule createDeltaModule()
  {
    DeltaModuleImpl deltaModule = new DeltaModuleImpl();
    return deltaModule;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public DeltaAction createDeltaAction()
  {
    DeltaActionImpl deltaAction = new DeltaActionImpl();
    return deltaAction;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public ClassAddition createClassAddition()
  {
    ClassAdditionImpl classAddition = new ClassAdditionImpl();
    return classAddition;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public RemovesOrModifiesClass createRemovesOrModifiesClass()
  {
    RemovesOrModifiesClassImpl removesOrModifiesClass = new RemovesOrModifiesClassImpl();
    return removesOrModifiesClass;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public ClassRemoval createClassRemoval()
  {
    ClassRemovalImpl classRemoval = new ClassRemovalImpl();
    return classRemoval;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public ClassModification createClassModification()
  {
    ClassModificationImpl classModification = new ClassModificationImpl();
    return classModification;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public DeltaSubAction createDeltaSubAction()
  {
    DeltaSubActionImpl deltaSubAction = new DeltaSubActionImpl();
    return deltaSubAction;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public MethodOrFieldAddition createMethodOrFieldAddition()
  {
    MethodOrFieldAdditionImpl methodOrFieldAddition = new MethodOrFieldAdditionImpl();
    return methodOrFieldAddition;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public FieldAddition createFieldAddition()
  {
    FieldAdditionImpl fieldAddition = new FieldAdditionImpl();
    return fieldAddition;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public MethodAddition createMethodAddition()
  {
    MethodAdditionImpl methodAddition = new MethodAdditionImpl();
    return methodAddition;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public FieldRemoval createFieldRemoval()
  {
    FieldRemovalImpl fieldRemoval = new FieldRemovalImpl();
    return fieldRemoval;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public MethodRemoval createMethodRemoval()
  {
    MethodRemovalImpl methodRemoval = new MethodRemovalImpl();
    return methodRemoval;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public MethodModification createMethodModification()
  {
    MethodModificationImpl methodModification = new MethodModificationImpl();
    return methodModification;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public ProductLine createProductLine()
  {
    ProductLineImpl productLine = new ProductLineImpl();
    return productLine;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public Features createFeatures()
  {
    FeaturesImpl features = new FeaturesImpl();
    return features;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public Feature createFeature()
  {
    FeatureImpl feature = new FeatureImpl();
    return feature;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public Configurations createConfigurations()
  {
    ConfigurationsImpl configurations = new ConfigurationsImpl();
    return configurations;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public Configuration createConfiguration()
  {
    ConfigurationImpl configuration = new ConfigurationImpl();
    return configuration;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public DeltaPartition createDeltaPartition()
  {
    DeltaPartitionImpl deltaPartition = new DeltaPartitionImpl();
    return deltaPartition;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public PartitionPart createPartitionPart()
  {
    PartitionPartImpl partitionPart = new PartitionPartImpl();
    return partitionPart;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public ModuleReference createModuleReference()
  {
    ModuleReferenceImpl moduleReference = new ModuleReferenceImpl();
    return moduleReference;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public PropositionalFormula createPropositionalFormula()
  {
    PropositionalFormulaImpl propositionalFormula = new PropositionalFormulaImpl();
    return propositionalFormula;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public Product createProduct()
  {
    ProductImpl product = new ProductImpl();
    return product;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public ReturnStatement createReturnStatement()
  {
    ReturnStatementImpl returnStatement = new ReturnStatementImpl();
    return returnStatement;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public JavaVerbatim createJavaVerbatim()
  {
    JavaVerbatimImpl javaVerbatim = new JavaVerbatimImpl();
    return javaVerbatim;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public Plus createPlus()
  {
    PlusImpl plus = new PlusImpl();
    return plus;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public Minus createMinus()
  {
    MinusImpl minus = new MinusImpl();
    return minus;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public MultiOrDiv createMultiOrDiv()
  {
    MultiOrDivImpl multiOrDiv = new MultiOrDivImpl();
    return multiOrDiv;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public Comparison createComparison()
  {
    ComparisonImpl comparison = new ComparisonImpl();
    return comparison;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public AndOrExpression createAndOrExpression()
  {
    AndOrExpressionImpl andOrExpression = new AndOrExpressionImpl();
    return andOrExpression;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public BooleanNegation createBooleanNegation()
  {
    BooleanNegationImpl booleanNegation = new BooleanNegationImpl();
    return booleanNegation;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public ArithmeticSigned createArithmeticSigned()
  {
    ArithmeticSignedImpl arithmeticSigned = new ArithmeticSignedImpl();
    return arithmeticSigned;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public Selection createSelection()
  {
    SelectionImpl selection = new SelectionImpl();
    return selection;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public Or createOr()
  {
    OrImpl or = new OrImpl();
    return or;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public And createAnd()
  {
    AndImpl and = new AndImpl();
    return and;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public FeatureRef createFeatureRef()
  {
    FeatureRefImpl featureRef = new FeatureRefImpl();
    return featureRef;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public PropParen createPropParen()
  {
    PropParenImpl propParen = new PropParenImpl();
    return propParen;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public Negation createNegation()
  {
    NegationImpl negation = new NegationImpl();
    return negation;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public PropTrue createPropTrue()
  {
    PropTrueImpl propTrue = new PropTrueImpl();
    return propTrue;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public PropFalse createPropFalse()
  {
    PropFalseImpl propFalse = new PropFalseImpl();
    return propFalse;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public DeltajPackage getDeltajPackage()
  {
    return (DeltajPackage)getEPackage();
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @deprecated
   * @generated
   */
  @Deprecated
  public static DeltajPackage getPackage()
  {
    return DeltajPackage.eINSTANCE;
  }

} //DeltajFactoryImpl
