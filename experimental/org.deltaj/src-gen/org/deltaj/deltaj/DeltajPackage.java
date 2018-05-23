/**
 * <copyright>
 * </copyright>
 *
 */
package org.deltaj.deltaj;

import org.eclipse.emf.ecore.EAttribute;
import org.eclipse.emf.ecore.EClass;
import org.eclipse.emf.ecore.EPackage;
import org.eclipse.emf.ecore.EReference;

/**
 * <!-- begin-user-doc -->
 * The <b>Package</b> for the model.
 * It contains accessors for the meta objects to represent
 * <ul>
 *   <li>each class,</li>
 *   <li>each feature of each class,</li>
 *   <li>each enum,</li>
 *   <li>and each data type</li>
 * </ul>
 * <!-- end-user-doc -->
 * @see org.deltaj.deltaj.DeltajFactory
 * @model kind="package"
 * @generated
 */
public interface DeltajPackage extends EPackage
{
  /**
   * The package name.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  String eNAME = "deltaj";

  /**
   * The package namespace URI.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  String eNS_URI = "http://www.deltaj.org/DeltaJ";

  /**
   * The package namespace name.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  String eNS_PREFIX = "deltaj";

  /**
   * The singleton instance of the package.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  DeltajPackage eINSTANCE = org.deltaj.deltaj.impl.DeltajPackageImpl.init();

  /**
   * The meta object id for the '{@link org.deltaj.deltaj.impl.ProgramImpl <em>Program</em>}' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see org.deltaj.deltaj.impl.ProgramImpl
   * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getProgram()
   * @generated
   */
  int PROGRAM = 0;

  /**
   * The feature id for the '<em><b>Delta Modules</b></em>' containment reference list.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int PROGRAM__DELTA_MODULES = 0;

  /**
   * The feature id for the '<em><b>Product Lines</b></em>' containment reference list.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int PROGRAM__PRODUCT_LINES = 1;

  /**
   * The feature id for the '<em><b>Products</b></em>' containment reference list.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int PROGRAM__PRODUCTS = 2;

  /**
   * The number of structural features of the '<em>Program</em>' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int PROGRAM_FEATURE_COUNT = 3;

  /**
   * The meta object id for the '{@link org.deltaj.deltaj.impl.TypeImpl <em>Type</em>}' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see org.deltaj.deltaj.impl.TypeImpl
   * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getType()
   * @generated
   */
  int TYPE = 1;

  /**
   * The number of structural features of the '<em>Type</em>' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int TYPE_FEATURE_COUNT = 0;

  /**
   * The meta object id for the '{@link org.deltaj.deltaj.impl.TypeVariableImpl <em>Type Variable</em>}' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see org.deltaj.deltaj.impl.TypeVariableImpl
   * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getTypeVariable()
   * @generated
   */
  int TYPE_VARIABLE = 2;

  /**
   * The feature id for the '<em><b>Var Name</b></em>' attribute.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int TYPE_VARIABLE__VAR_NAME = TYPE_FEATURE_COUNT + 0;

  /**
   * The number of structural features of the '<em>Type Variable</em>' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int TYPE_VARIABLE_FEATURE_COUNT = TYPE_FEATURE_COUNT + 1;

  /**
   * The meta object id for the '{@link org.deltaj.deltaj.impl.TypeForMethodImpl <em>Type For Method</em>}' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see org.deltaj.deltaj.impl.TypeForMethodImpl
   * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getTypeForMethod()
   * @generated
   */
  int TYPE_FOR_METHOD = 3;

  /**
   * The number of structural features of the '<em>Type For Method</em>' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int TYPE_FOR_METHOD_FEATURE_COUNT = TYPE_FEATURE_COUNT + 0;

  /**
   * The meta object id for the '{@link org.deltaj.deltaj.impl.VoidTypeImpl <em>Void Type</em>}' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see org.deltaj.deltaj.impl.VoidTypeImpl
   * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getVoidType()
   * @generated
   */
  int VOID_TYPE = 4;

  /**
   * The feature id for the '<em><b>Void</b></em>' attribute.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int VOID_TYPE__VOID = TYPE_FOR_METHOD_FEATURE_COUNT + 0;

  /**
   * The number of structural features of the '<em>Void Type</em>' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int VOID_TYPE_FEATURE_COUNT = TYPE_FOR_METHOD_FEATURE_COUNT + 1;

  /**
   * The meta object id for the '{@link org.deltaj.deltaj.impl.TypeForDeclarationImpl <em>Type For Declaration</em>}' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see org.deltaj.deltaj.impl.TypeForDeclarationImpl
   * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getTypeForDeclaration()
   * @generated
   */
  int TYPE_FOR_DECLARATION = 5;

  /**
   * The number of structural features of the '<em>Type For Declaration</em>' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int TYPE_FOR_DECLARATION_FEATURE_COUNT = TYPE_FOR_METHOD_FEATURE_COUNT + 0;

  /**
   * The meta object id for the '{@link org.deltaj.deltaj.impl.BasicTypeImpl <em>Basic Type</em>}' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see org.deltaj.deltaj.impl.BasicTypeImpl
   * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getBasicType()
   * @generated
   */
  int BASIC_TYPE = 6;

  /**
   * The feature id for the '<em><b>Basic</b></em>' attribute.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int BASIC_TYPE__BASIC = TYPE_FOR_DECLARATION_FEATURE_COUNT + 0;

  /**
   * The number of structural features of the '<em>Basic Type</em>' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int BASIC_TYPE_FEATURE_COUNT = TYPE_FOR_DECLARATION_FEATURE_COUNT + 1;

  /**
   * The meta object id for the '{@link org.deltaj.deltaj.impl.IntTypeImpl <em>Int Type</em>}' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see org.deltaj.deltaj.impl.IntTypeImpl
   * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getIntType()
   * @generated
   */
  int INT_TYPE = 7;

  /**
   * The feature id for the '<em><b>Basic</b></em>' attribute.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int INT_TYPE__BASIC = BASIC_TYPE__BASIC;

  /**
   * The number of structural features of the '<em>Int Type</em>' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int INT_TYPE_FEATURE_COUNT = BASIC_TYPE_FEATURE_COUNT + 0;

  /**
   * The meta object id for the '{@link org.deltaj.deltaj.impl.BooleanTypeImpl <em>Boolean Type</em>}' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see org.deltaj.deltaj.impl.BooleanTypeImpl
   * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getBooleanType()
   * @generated
   */
  int BOOLEAN_TYPE = 8;

  /**
   * The feature id for the '<em><b>Basic</b></em>' attribute.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int BOOLEAN_TYPE__BASIC = BASIC_TYPE__BASIC;

  /**
   * The number of structural features of the '<em>Boolean Type</em>' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int BOOLEAN_TYPE_FEATURE_COUNT = BASIC_TYPE_FEATURE_COUNT + 0;

  /**
   * The meta object id for the '{@link org.deltaj.deltaj.impl.StringTypeImpl <em>String Type</em>}' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see org.deltaj.deltaj.impl.StringTypeImpl
   * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getStringType()
   * @generated
   */
  int STRING_TYPE = 9;

  /**
   * The feature id for the '<em><b>Basic</b></em>' attribute.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int STRING_TYPE__BASIC = BASIC_TYPE__BASIC;

  /**
   * The number of structural features of the '<em>String Type</em>' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int STRING_TYPE_FEATURE_COUNT = BASIC_TYPE_FEATURE_COUNT + 0;

  /**
   * The meta object id for the '{@link org.deltaj.deltaj.impl.ClassTypeImpl <em>Class Type</em>}' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see org.deltaj.deltaj.impl.ClassTypeImpl
   * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getClassType()
   * @generated
   */
  int CLASS_TYPE = 10;

  /**
   * The feature id for the '<em><b>Classref</b></em>' attribute.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int CLASS_TYPE__CLASSREF = TYPE_FOR_DECLARATION_FEATURE_COUNT + 0;

  /**
   * The number of structural features of the '<em>Class Type</em>' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int CLASS_TYPE_FEATURE_COUNT = TYPE_FOR_DECLARATION_FEATURE_COUNT + 1;

  /**
   * The meta object id for the '{@link org.deltaj.deltaj.impl.ClassImpl <em>Class</em>}' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see org.deltaj.deltaj.impl.ClassImpl
   * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getClass_()
   * @generated
   */
  int CLASS = 11;

  /**
   * The feature id for the '<em><b>Name</b></em>' attribute.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int CLASS__NAME = 0;

  /**
   * The feature id for the '<em><b>Extends</b></em>' attribute.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int CLASS__EXTENDS = 1;

  /**
   * The feature id for the '<em><b>Fields</b></em>' containment reference list.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int CLASS__FIELDS = 2;

  /**
   * The feature id for the '<em><b>Methods</b></em>' containment reference list.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int CLASS__METHODS = 3;

  /**
   * The number of structural features of the '<em>Class</em>' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int CLASS_FEATURE_COUNT = 4;

  /**
   * The meta object id for the '{@link org.deltaj.deltaj.impl.TypedDeclarationImpl <em>Typed Declaration</em>}' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see org.deltaj.deltaj.impl.TypedDeclarationImpl
   * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getTypedDeclaration()
   * @generated
   */
  int TYPED_DECLARATION = 12;

  /**
   * The feature id for the '<em><b>Type</b></em>' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int TYPED_DECLARATION__TYPE = 0;

  /**
   * The feature id for the '<em><b>Name</b></em>' attribute.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int TYPED_DECLARATION__NAME = 1;

  /**
   * The number of structural features of the '<em>Typed Declaration</em>' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int TYPED_DECLARATION_FEATURE_COUNT = 2;

  /**
   * The meta object id for the '{@link org.deltaj.deltaj.impl.FieldImpl <em>Field</em>}' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see org.deltaj.deltaj.impl.FieldImpl
   * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getField()
   * @generated
   */
  int FIELD = 13;

  /**
   * The feature id for the '<em><b>Type</b></em>' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int FIELD__TYPE = TYPED_DECLARATION__TYPE;

  /**
   * The feature id for the '<em><b>Name</b></em>' attribute.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int FIELD__NAME = TYPED_DECLARATION__NAME;

  /**
   * The number of structural features of the '<em>Field</em>' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int FIELD_FEATURE_COUNT = TYPED_DECLARATION_FEATURE_COUNT + 0;

  /**
   * The meta object id for the '{@link org.deltaj.deltaj.impl.LocalVariableDeclarationImpl <em>Local Variable Declaration</em>}' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see org.deltaj.deltaj.impl.LocalVariableDeclarationImpl
   * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getLocalVariableDeclaration()
   * @generated
   */
  int LOCAL_VARIABLE_DECLARATION = 14;

  /**
   * The feature id for the '<em><b>Type</b></em>' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int LOCAL_VARIABLE_DECLARATION__TYPE = TYPED_DECLARATION__TYPE;

  /**
   * The feature id for the '<em><b>Name</b></em>' attribute.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int LOCAL_VARIABLE_DECLARATION__NAME = TYPED_DECLARATION__NAME;

  /**
   * The number of structural features of the '<em>Local Variable Declaration</em>' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int LOCAL_VARIABLE_DECLARATION_FEATURE_COUNT = TYPED_DECLARATION_FEATURE_COUNT + 0;

  /**
   * The meta object id for the '{@link org.deltaj.deltaj.impl.ParameterImpl <em>Parameter</em>}' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see org.deltaj.deltaj.impl.ParameterImpl
   * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getParameter()
   * @generated
   */
  int PARAMETER = 15;

  /**
   * The feature id for the '<em><b>Type</b></em>' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int PARAMETER__TYPE = TYPED_DECLARATION__TYPE;

  /**
   * The feature id for the '<em><b>Name</b></em>' attribute.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int PARAMETER__NAME = TYPED_DECLARATION__NAME;

  /**
   * The number of structural features of the '<em>Parameter</em>' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int PARAMETER_FEATURE_COUNT = TYPED_DECLARATION_FEATURE_COUNT + 0;

  /**
   * The meta object id for the '{@link org.deltaj.deltaj.impl.MethodImpl <em>Method</em>}' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see org.deltaj.deltaj.impl.MethodImpl
   * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getMethod()
   * @generated
   */
  int METHOD = 16;

  /**
   * The feature id for the '<em><b>Returntype</b></em>' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int METHOD__RETURNTYPE = 0;

  /**
   * The feature id for the '<em><b>Name</b></em>' attribute.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int METHOD__NAME = 1;

  /**
   * The feature id for the '<em><b>Params</b></em>' containment reference list.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int METHOD__PARAMS = 2;

  /**
   * The feature id for the '<em><b>Body</b></em>' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int METHOD__BODY = 3;

  /**
   * The number of structural features of the '<em>Method</em>' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int METHOD_FEATURE_COUNT = 4;

  /**
   * The meta object id for the '{@link org.deltaj.deltaj.impl.StatementBlockImpl <em>Statement Block</em>}' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see org.deltaj.deltaj.impl.StatementBlockImpl
   * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getStatementBlock()
   * @generated
   */
  int STATEMENT_BLOCK = 17;

  /**
   * The feature id for the '<em><b>Localvariables</b></em>' containment reference list.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int STATEMENT_BLOCK__LOCALVARIABLES = 0;

  /**
   * The feature id for the '<em><b>Statements</b></em>' containment reference list.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int STATEMENT_BLOCK__STATEMENTS = 1;

  /**
   * The number of structural features of the '<em>Statement Block</em>' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int STATEMENT_BLOCK_FEATURE_COUNT = 2;

  /**
   * The meta object id for the '{@link org.deltaj.deltaj.impl.StatementImpl <em>Statement</em>}' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see org.deltaj.deltaj.impl.StatementImpl
   * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getStatement()
   * @generated
   */
  int STATEMENT = 18;

  /**
   * The number of structural features of the '<em>Statement</em>' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int STATEMENT_FEATURE_COUNT = 0;

  /**
   * The meta object id for the '{@link org.deltaj.deltaj.impl.ExpressionStatementImpl <em>Expression Statement</em>}' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see org.deltaj.deltaj.impl.ExpressionStatementImpl
   * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getExpressionStatement()
   * @generated
   */
  int EXPRESSION_STATEMENT = 19;

  /**
   * The feature id for the '<em><b>Expression</b></em>' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int EXPRESSION_STATEMENT__EXPRESSION = STATEMENT_FEATURE_COUNT + 0;

  /**
   * The number of structural features of the '<em>Expression Statement</em>' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int EXPRESSION_STATEMENT_FEATURE_COUNT = STATEMENT_FEATURE_COUNT + 1;

  /**
   * The meta object id for the '{@link org.deltaj.deltaj.impl.AssignmentImpl <em>Assignment</em>}' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see org.deltaj.deltaj.impl.AssignmentImpl
   * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getAssignment()
   * @generated
   */
  int ASSIGNMENT = 20;

  /**
   * The feature id for the '<em><b>Left</b></em>' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int ASSIGNMENT__LEFT = STATEMENT_FEATURE_COUNT + 0;

  /**
   * The feature id for the '<em><b>Right</b></em>' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int ASSIGNMENT__RIGHT = STATEMENT_FEATURE_COUNT + 1;

  /**
   * The number of structural features of the '<em>Assignment</em>' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int ASSIGNMENT_FEATURE_COUNT = STATEMENT_FEATURE_COUNT + 2;

  /**
   * The meta object id for the '{@link org.deltaj.deltaj.impl.IfStatementImpl <em>If Statement</em>}' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see org.deltaj.deltaj.impl.IfStatementImpl
   * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getIfStatement()
   * @generated
   */
  int IF_STATEMENT = 21;

  /**
   * The feature id for the '<em><b>Expression</b></em>' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int IF_STATEMENT__EXPRESSION = STATEMENT_FEATURE_COUNT + 0;

  /**
   * The feature id for the '<em><b>Then Block</b></em>' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int IF_STATEMENT__THEN_BLOCK = STATEMENT_FEATURE_COUNT + 1;

  /**
   * The feature id for the '<em><b>Else Block</b></em>' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int IF_STATEMENT__ELSE_BLOCK = STATEMENT_FEATURE_COUNT + 2;

  /**
   * The number of structural features of the '<em>If Statement</em>' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int IF_STATEMENT_FEATURE_COUNT = STATEMENT_FEATURE_COUNT + 3;

  /**
   * The meta object id for the '{@link org.deltaj.deltaj.impl.ExpressionImpl <em>Expression</em>}' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see org.deltaj.deltaj.impl.ExpressionImpl
   * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getExpression()
   * @generated
   */
  int EXPRESSION = 22;

  /**
   * The number of structural features of the '<em>Expression</em>' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int EXPRESSION_FEATURE_COUNT = 0;

  /**
   * The meta object id for the '{@link org.deltaj.deltaj.impl.NullImpl <em>Null</em>}' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see org.deltaj.deltaj.impl.NullImpl
   * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getNull()
   * @generated
   */
  int NULL = 23;

  /**
   * The feature id for the '<em><b>Null</b></em>' attribute.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int NULL__NULL = EXPRESSION_FEATURE_COUNT + 0;

  /**
   * The number of structural features of the '<em>Null</em>' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int NULL_FEATURE_COUNT = EXPRESSION_FEATURE_COUNT + 1;

  /**
   * The meta object id for the '{@link org.deltaj.deltaj.impl.ThisImpl <em>This</em>}' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see org.deltaj.deltaj.impl.ThisImpl
   * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getThis()
   * @generated
   */
  int THIS = 24;

  /**
   * The feature id for the '<em><b>Variable</b></em>' attribute.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int THIS__VARIABLE = EXPRESSION_FEATURE_COUNT + 0;

  /**
   * The number of structural features of the '<em>This</em>' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int THIS_FEATURE_COUNT = EXPRESSION_FEATURE_COUNT + 1;

  /**
   * The meta object id for the '{@link org.deltaj.deltaj.impl.OriginalImpl <em>Original</em>}' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see org.deltaj.deltaj.impl.OriginalImpl
   * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getOriginal()
   * @generated
   */
  int ORIGINAL = 25;

  /**
   * The feature id for the '<em><b>Method</b></em>' attribute.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int ORIGINAL__METHOD = EXPRESSION_FEATURE_COUNT + 0;

  /**
   * The feature id for the '<em><b>Args</b></em>' containment reference list.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int ORIGINAL__ARGS = EXPRESSION_FEATURE_COUNT + 1;

  /**
   * The number of structural features of the '<em>Original</em>' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int ORIGINAL_FEATURE_COUNT = EXPRESSION_FEATURE_COUNT + 2;

  /**
   * The meta object id for the '{@link org.deltaj.deltaj.impl.VariableAccessImpl <em>Variable Access</em>}' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see org.deltaj.deltaj.impl.VariableAccessImpl
   * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getVariableAccess()
   * @generated
   */
  int VARIABLE_ACCESS = 26;

  /**
   * The feature id for the '<em><b>Variable</b></em>' reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int VARIABLE_ACCESS__VARIABLE = EXPRESSION_FEATURE_COUNT + 0;

  /**
   * The number of structural features of the '<em>Variable Access</em>' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int VARIABLE_ACCESS_FEATURE_COUNT = EXPRESSION_FEATURE_COUNT + 1;

  /**
   * The meta object id for the '{@link org.deltaj.deltaj.impl.NewImpl <em>New</em>}' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see org.deltaj.deltaj.impl.NewImpl
   * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getNew()
   * @generated
   */
  int NEW = 27;

  /**
   * The feature id for the '<em><b>Class</b></em>' attribute.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int NEW__CLASS = EXPRESSION_FEATURE_COUNT + 0;

  /**
   * The number of structural features of the '<em>New</em>' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int NEW_FEATURE_COUNT = EXPRESSION_FEATURE_COUNT + 1;

  /**
   * The meta object id for the '{@link org.deltaj.deltaj.impl.CastImpl <em>Cast</em>}' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see org.deltaj.deltaj.impl.CastImpl
   * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getCast()
   * @generated
   */
  int CAST = 28;

  /**
   * The feature id for the '<em><b>Type</b></em>' attribute.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int CAST__TYPE = EXPRESSION_FEATURE_COUNT + 0;

  /**
   * The feature id for the '<em><b>Object</b></em>' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int CAST__OBJECT = EXPRESSION_FEATURE_COUNT + 1;

  /**
   * The number of structural features of the '<em>Cast</em>' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int CAST_FEATURE_COUNT = EXPRESSION_FEATURE_COUNT + 2;

  /**
   * The meta object id for the '{@link org.deltaj.deltaj.impl.ParenImpl <em>Paren</em>}' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see org.deltaj.deltaj.impl.ParenImpl
   * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getParen()
   * @generated
   */
  int PAREN = 29;

  /**
   * The feature id for the '<em><b>Expression</b></em>' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int PAREN__EXPRESSION = EXPRESSION_FEATURE_COUNT + 0;

  /**
   * The number of structural features of the '<em>Paren</em>' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int PAREN_FEATURE_COUNT = EXPRESSION_FEATURE_COUNT + 1;

  /**
   * The meta object id for the '{@link org.deltaj.deltaj.impl.ConstantImpl <em>Constant</em>}' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see org.deltaj.deltaj.impl.ConstantImpl
   * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getConstant()
   * @generated
   */
  int CONSTANT = 30;

  /**
   * The number of structural features of the '<em>Constant</em>' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int CONSTANT_FEATURE_COUNT = EXPRESSION_FEATURE_COUNT + 0;

  /**
   * The meta object id for the '{@link org.deltaj.deltaj.impl.StringConstantImpl <em>String Constant</em>}' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see org.deltaj.deltaj.impl.StringConstantImpl
   * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getStringConstant()
   * @generated
   */
  int STRING_CONSTANT = 31;

  /**
   * The feature id for the '<em><b>Constant</b></em>' attribute.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int STRING_CONSTANT__CONSTANT = CONSTANT_FEATURE_COUNT + 0;

  /**
   * The number of structural features of the '<em>String Constant</em>' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int STRING_CONSTANT_FEATURE_COUNT = CONSTANT_FEATURE_COUNT + 1;

  /**
   * The meta object id for the '{@link org.deltaj.deltaj.impl.IntConstantImpl <em>Int Constant</em>}' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see org.deltaj.deltaj.impl.IntConstantImpl
   * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getIntConstant()
   * @generated
   */
  int INT_CONSTANT = 32;

  /**
   * The feature id for the '<em><b>Constant</b></em>' attribute.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int INT_CONSTANT__CONSTANT = CONSTANT_FEATURE_COUNT + 0;

  /**
   * The number of structural features of the '<em>Int Constant</em>' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int INT_CONSTANT_FEATURE_COUNT = CONSTANT_FEATURE_COUNT + 1;

  /**
   * The meta object id for the '{@link org.deltaj.deltaj.impl.BoolConstantImpl <em>Bool Constant</em>}' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see org.deltaj.deltaj.impl.BoolConstantImpl
   * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getBoolConstant()
   * @generated
   */
  int BOOL_CONSTANT = 33;

  /**
   * The feature id for the '<em><b>Constant</b></em>' attribute.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int BOOL_CONSTANT__CONSTANT = CONSTANT_FEATURE_COUNT + 0;

  /**
   * The number of structural features of the '<em>Bool Constant</em>' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int BOOL_CONSTANT_FEATURE_COUNT = CONSTANT_FEATURE_COUNT + 1;

  /**
   * The meta object id for the '{@link org.deltaj.deltaj.impl.MessageImpl <em>Message</em>}' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see org.deltaj.deltaj.impl.MessageImpl
   * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getMessage()
   * @generated
   */
  int MESSAGE = 34;

  /**
   * The number of structural features of the '<em>Message</em>' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int MESSAGE_FEATURE_COUNT = 0;

  /**
   * The meta object id for the '{@link org.deltaj.deltaj.impl.MethodCallImpl <em>Method Call</em>}' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see org.deltaj.deltaj.impl.MethodCallImpl
   * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getMethodCall()
   * @generated
   */
  int METHOD_CALL = 35;

  /**
   * The feature id for the '<em><b>Method</b></em>' attribute.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int METHOD_CALL__METHOD = MESSAGE_FEATURE_COUNT + 0;

  /**
   * The feature id for the '<em><b>Args</b></em>' containment reference list.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int METHOD_CALL__ARGS = MESSAGE_FEATURE_COUNT + 1;

  /**
   * The number of structural features of the '<em>Method Call</em>' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int METHOD_CALL_FEATURE_COUNT = MESSAGE_FEATURE_COUNT + 2;

  /**
   * The meta object id for the '{@link org.deltaj.deltaj.impl.FieldSelectionImpl <em>Field Selection</em>}' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see org.deltaj.deltaj.impl.FieldSelectionImpl
   * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getFieldSelection()
   * @generated
   */
  int FIELD_SELECTION = 36;

  /**
   * The feature id for the '<em><b>Field</b></em>' attribute.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int FIELD_SELECTION__FIELD = MESSAGE_FEATURE_COUNT + 0;

  /**
   * The number of structural features of the '<em>Field Selection</em>' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int FIELD_SELECTION_FEATURE_COUNT = MESSAGE_FEATURE_COUNT + 1;

  /**
   * The meta object id for the '{@link org.deltaj.deltaj.impl.DeltaModuleImpl <em>Delta Module</em>}' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see org.deltaj.deltaj.impl.DeltaModuleImpl
   * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getDeltaModule()
   * @generated
   */
  int DELTA_MODULE = 37;

  /**
   * The feature id for the '<em><b>Name</b></em>' attribute.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int DELTA_MODULE__NAME = 0;

  /**
   * The feature id for the '<em><b>Delta Actions</b></em>' containment reference list.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int DELTA_MODULE__DELTA_ACTIONS = 1;

  /**
   * The number of structural features of the '<em>Delta Module</em>' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int DELTA_MODULE_FEATURE_COUNT = 2;

  /**
   * The meta object id for the '{@link org.deltaj.deltaj.impl.DeltaActionImpl <em>Delta Action</em>}' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see org.deltaj.deltaj.impl.DeltaActionImpl
   * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getDeltaAction()
   * @generated
   */
  int DELTA_ACTION = 38;

  /**
   * The number of structural features of the '<em>Delta Action</em>' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int DELTA_ACTION_FEATURE_COUNT = 0;

  /**
   * The meta object id for the '{@link org.deltaj.deltaj.impl.ClassAdditionImpl <em>Class Addition</em>}' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see org.deltaj.deltaj.impl.ClassAdditionImpl
   * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getClassAddition()
   * @generated
   */
  int CLASS_ADDITION = 39;

  /**
   * The feature id for the '<em><b>Class</b></em>' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int CLASS_ADDITION__CLASS = DELTA_ACTION_FEATURE_COUNT + 0;

  /**
   * The number of structural features of the '<em>Class Addition</em>' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int CLASS_ADDITION_FEATURE_COUNT = DELTA_ACTION_FEATURE_COUNT + 1;

  /**
   * The meta object id for the '{@link org.deltaj.deltaj.impl.RemovesOrModifiesClassImpl <em>Removes Or Modifies Class</em>}' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see org.deltaj.deltaj.impl.RemovesOrModifiesClassImpl
   * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getRemovesOrModifiesClass()
   * @generated
   */
  int REMOVES_OR_MODIFIES_CLASS = 40;

  /**
   * The feature id for the '<em><b>Name</b></em>' attribute.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int REMOVES_OR_MODIFIES_CLASS__NAME = DELTA_ACTION_FEATURE_COUNT + 0;

  /**
   * The number of structural features of the '<em>Removes Or Modifies Class</em>' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int REMOVES_OR_MODIFIES_CLASS_FEATURE_COUNT = DELTA_ACTION_FEATURE_COUNT + 1;

  /**
   * The meta object id for the '{@link org.deltaj.deltaj.impl.ClassRemovalImpl <em>Class Removal</em>}' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see org.deltaj.deltaj.impl.ClassRemovalImpl
   * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getClassRemoval()
   * @generated
   */
  int CLASS_REMOVAL = 41;

  /**
   * The feature id for the '<em><b>Name</b></em>' attribute.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int CLASS_REMOVAL__NAME = REMOVES_OR_MODIFIES_CLASS__NAME;

  /**
   * The number of structural features of the '<em>Class Removal</em>' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int CLASS_REMOVAL_FEATURE_COUNT = REMOVES_OR_MODIFIES_CLASS_FEATURE_COUNT + 0;

  /**
   * The meta object id for the '{@link org.deltaj.deltaj.impl.ClassModificationImpl <em>Class Modification</em>}' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see org.deltaj.deltaj.impl.ClassModificationImpl
   * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getClassModification()
   * @generated
   */
  int CLASS_MODIFICATION = 42;

  /**
   * The feature id for the '<em><b>Name</b></em>' attribute.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int CLASS_MODIFICATION__NAME = REMOVES_OR_MODIFIES_CLASS__NAME;

  /**
   * The feature id for the '<em><b>Extends</b></em>' attribute.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int CLASS_MODIFICATION__EXTENDS = REMOVES_OR_MODIFIES_CLASS_FEATURE_COUNT + 0;

  /**
   * The feature id for the '<em><b>Sub Actions</b></em>' containment reference list.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int CLASS_MODIFICATION__SUB_ACTIONS = REMOVES_OR_MODIFIES_CLASS_FEATURE_COUNT + 1;

  /**
   * The number of structural features of the '<em>Class Modification</em>' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int CLASS_MODIFICATION_FEATURE_COUNT = REMOVES_OR_MODIFIES_CLASS_FEATURE_COUNT + 2;

  /**
   * The meta object id for the '{@link org.deltaj.deltaj.impl.DeltaSubActionImpl <em>Delta Sub Action</em>}' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see org.deltaj.deltaj.impl.DeltaSubActionImpl
   * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getDeltaSubAction()
   * @generated
   */
  int DELTA_SUB_ACTION = 43;

  /**
   * The number of structural features of the '<em>Delta Sub Action</em>' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int DELTA_SUB_ACTION_FEATURE_COUNT = 0;

  /**
   * The meta object id for the '{@link org.deltaj.deltaj.impl.MethodOrFieldAdditionImpl <em>Method Or Field Addition</em>}' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see org.deltaj.deltaj.impl.MethodOrFieldAdditionImpl
   * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getMethodOrFieldAddition()
   * @generated
   */
  int METHOD_OR_FIELD_ADDITION = 44;

  /**
   * The number of structural features of the '<em>Method Or Field Addition</em>' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int METHOD_OR_FIELD_ADDITION_FEATURE_COUNT = DELTA_SUB_ACTION_FEATURE_COUNT + 0;

  /**
   * The meta object id for the '{@link org.deltaj.deltaj.impl.FieldAdditionImpl <em>Field Addition</em>}' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see org.deltaj.deltaj.impl.FieldAdditionImpl
   * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getFieldAddition()
   * @generated
   */
  int FIELD_ADDITION = 45;

  /**
   * The feature id for the '<em><b>Field</b></em>' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int FIELD_ADDITION__FIELD = METHOD_OR_FIELD_ADDITION_FEATURE_COUNT + 0;

  /**
   * The number of structural features of the '<em>Field Addition</em>' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int FIELD_ADDITION_FEATURE_COUNT = METHOD_OR_FIELD_ADDITION_FEATURE_COUNT + 1;

  /**
   * The meta object id for the '{@link org.deltaj.deltaj.impl.MethodAdditionImpl <em>Method Addition</em>}' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see org.deltaj.deltaj.impl.MethodAdditionImpl
   * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getMethodAddition()
   * @generated
   */
  int METHOD_ADDITION = 46;

  /**
   * The feature id for the '<em><b>Method</b></em>' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int METHOD_ADDITION__METHOD = METHOD_OR_FIELD_ADDITION_FEATURE_COUNT + 0;

  /**
   * The number of structural features of the '<em>Method Addition</em>' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int METHOD_ADDITION_FEATURE_COUNT = METHOD_OR_FIELD_ADDITION_FEATURE_COUNT + 1;

  /**
   * The meta object id for the '{@link org.deltaj.deltaj.impl.FieldRemovalImpl <em>Field Removal</em>}' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see org.deltaj.deltaj.impl.FieldRemovalImpl
   * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getFieldRemoval()
   * @generated
   */
  int FIELD_REMOVAL = 47;

  /**
   * The feature id for the '<em><b>Name</b></em>' attribute.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int FIELD_REMOVAL__NAME = DELTA_SUB_ACTION_FEATURE_COUNT + 0;

  /**
   * The number of structural features of the '<em>Field Removal</em>' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int FIELD_REMOVAL_FEATURE_COUNT = DELTA_SUB_ACTION_FEATURE_COUNT + 1;

  /**
   * The meta object id for the '{@link org.deltaj.deltaj.impl.MethodRemovalImpl <em>Method Removal</em>}' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see org.deltaj.deltaj.impl.MethodRemovalImpl
   * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getMethodRemoval()
   * @generated
   */
  int METHOD_REMOVAL = 48;

  /**
   * The feature id for the '<em><b>Name</b></em>' attribute.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int METHOD_REMOVAL__NAME = DELTA_SUB_ACTION_FEATURE_COUNT + 0;

  /**
   * The number of structural features of the '<em>Method Removal</em>' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int METHOD_REMOVAL_FEATURE_COUNT = DELTA_SUB_ACTION_FEATURE_COUNT + 1;

  /**
   * The meta object id for the '{@link org.deltaj.deltaj.impl.MethodModificationImpl <em>Method Modification</em>}' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see org.deltaj.deltaj.impl.MethodModificationImpl
   * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getMethodModification()
   * @generated
   */
  int METHOD_MODIFICATION = 49;

  /**
   * The feature id for the '<em><b>Method</b></em>' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int METHOD_MODIFICATION__METHOD = DELTA_SUB_ACTION_FEATURE_COUNT + 0;

  /**
   * The number of structural features of the '<em>Method Modification</em>' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int METHOD_MODIFICATION_FEATURE_COUNT = DELTA_SUB_ACTION_FEATURE_COUNT + 1;

  /**
   * The meta object id for the '{@link org.deltaj.deltaj.impl.ProductLineImpl <em>Product Line</em>}' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see org.deltaj.deltaj.impl.ProductLineImpl
   * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getProductLine()
   * @generated
   */
  int PRODUCT_LINE = 50;

  /**
   * The feature id for the '<em><b>Name</b></em>' attribute.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int PRODUCT_LINE__NAME = 0;

  /**
   * The feature id for the '<em><b>Features</b></em>' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int PRODUCT_LINE__FEATURES = 1;

  /**
   * The feature id for the '<em><b>Configurations</b></em>' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int PRODUCT_LINE__CONFIGURATIONS = 2;

  /**
   * The feature id for the '<em><b>Partition</b></em>' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int PRODUCT_LINE__PARTITION = 3;

  /**
   * The number of structural features of the '<em>Product Line</em>' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int PRODUCT_LINE_FEATURE_COUNT = 4;

  /**
   * The meta object id for the '{@link org.deltaj.deltaj.impl.FeaturesImpl <em>Features</em>}' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see org.deltaj.deltaj.impl.FeaturesImpl
   * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getFeatures()
   * @generated
   */
  int FEATURES = 51;

  /**
   * The feature id for the '<em><b>Features List</b></em>' containment reference list.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int FEATURES__FEATURES_LIST = 0;

  /**
   * The number of structural features of the '<em>Features</em>' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int FEATURES_FEATURE_COUNT = 1;

  /**
   * The meta object id for the '{@link org.deltaj.deltaj.impl.FeatureImpl <em>Feature</em>}' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see org.deltaj.deltaj.impl.FeatureImpl
   * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getFeature()
   * @generated
   */
  int FEATURE = 52;

  /**
   * The feature id for the '<em><b>Name</b></em>' attribute.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int FEATURE__NAME = 0;

  /**
   * The number of structural features of the '<em>Feature</em>' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int FEATURE_FEATURE_COUNT = 1;

  /**
   * The meta object id for the '{@link org.deltaj.deltaj.impl.ConfigurationsImpl <em>Configurations</em>}' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see org.deltaj.deltaj.impl.ConfigurationsImpl
   * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getConfigurations()
   * @generated
   */
  int CONFIGURATIONS = 53;

  /**
   * The feature id for the '<em><b>Configurations</b></em>' containment reference list.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int CONFIGURATIONS__CONFIGURATIONS = 0;

  /**
   * The number of structural features of the '<em>Configurations</em>' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int CONFIGURATIONS_FEATURE_COUNT = 1;

  /**
   * The meta object id for the '{@link org.deltaj.deltaj.impl.ConfigurationImpl <em>Configuration</em>}' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see org.deltaj.deltaj.impl.ConfigurationImpl
   * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getConfiguration()
   * @generated
   */
  int CONFIGURATION = 54;

  /**
   * The feature id for the '<em><b>Formula</b></em>' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int CONFIGURATION__FORMULA = 0;

  /**
   * The number of structural features of the '<em>Configuration</em>' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int CONFIGURATION_FEATURE_COUNT = 1;

  /**
   * The meta object id for the '{@link org.deltaj.deltaj.impl.DeltaPartitionImpl <em>Delta Partition</em>}' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see org.deltaj.deltaj.impl.DeltaPartitionImpl
   * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getDeltaPartition()
   * @generated
   */
  int DELTA_PARTITION = 55;

  /**
   * The feature id for the '<em><b>Parts</b></em>' containment reference list.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int DELTA_PARTITION__PARTS = 0;

  /**
   * The number of structural features of the '<em>Delta Partition</em>' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int DELTA_PARTITION_FEATURE_COUNT = 1;

  /**
   * The meta object id for the '{@link org.deltaj.deltaj.impl.PartitionPartImpl <em>Partition Part</em>}' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see org.deltaj.deltaj.impl.PartitionPartImpl
   * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getPartitionPart()
   * @generated
   */
  int PARTITION_PART = 56;

  /**
   * The feature id for the '<em><b>Module References</b></em>' containment reference list.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int PARTITION_PART__MODULE_REFERENCES = 0;

  /**
   * The number of structural features of the '<em>Partition Part</em>' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int PARTITION_PART_FEATURE_COUNT = 1;

  /**
   * The meta object id for the '{@link org.deltaj.deltaj.impl.ModuleReferenceImpl <em>Module Reference</em>}' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see org.deltaj.deltaj.impl.ModuleReferenceImpl
   * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getModuleReference()
   * @generated
   */
  int MODULE_REFERENCE = 57;

  /**
   * The feature id for the '<em><b>Delta Module</b></em>' reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int MODULE_REFERENCE__DELTA_MODULE = 0;

  /**
   * The feature id for the '<em><b>When</b></em>' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int MODULE_REFERENCE__WHEN = 1;

  /**
   * The number of structural features of the '<em>Module Reference</em>' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int MODULE_REFERENCE_FEATURE_COUNT = 2;

  /**
   * The meta object id for the '{@link org.deltaj.deltaj.impl.PropositionalFormulaImpl <em>Propositional Formula</em>}' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see org.deltaj.deltaj.impl.PropositionalFormulaImpl
   * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getPropositionalFormula()
   * @generated
   */
  int PROPOSITIONAL_FORMULA = 58;

  /**
   * The number of structural features of the '<em>Propositional Formula</em>' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int PROPOSITIONAL_FORMULA_FEATURE_COUNT = 0;

  /**
   * The meta object id for the '{@link org.deltaj.deltaj.impl.ProductImpl <em>Product</em>}' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see org.deltaj.deltaj.impl.ProductImpl
   * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getProduct()
   * @generated
   */
  int PRODUCT = 59;

  /**
   * The feature id for the '<em><b>Name</b></em>' attribute.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int PRODUCT__NAME = 0;

  /**
   * The feature id for the '<em><b>Product Line</b></em>' reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int PRODUCT__PRODUCT_LINE = 1;

  /**
   * The feature id for the '<em><b>Features</b></em>' reference list.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int PRODUCT__FEATURES = 2;

  /**
   * The number of structural features of the '<em>Product</em>' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int PRODUCT_FEATURE_COUNT = 3;

  /**
   * The meta object id for the '{@link org.deltaj.deltaj.impl.ReturnStatementImpl <em>Return Statement</em>}' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see org.deltaj.deltaj.impl.ReturnStatementImpl
   * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getReturnStatement()
   * @generated
   */
  int RETURN_STATEMENT = 60;

  /**
   * The feature id for the '<em><b>Expression</b></em>' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int RETURN_STATEMENT__EXPRESSION = STATEMENT_FEATURE_COUNT + 0;

  /**
   * The number of structural features of the '<em>Return Statement</em>' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int RETURN_STATEMENT_FEATURE_COUNT = STATEMENT_FEATURE_COUNT + 1;

  /**
   * The meta object id for the '{@link org.deltaj.deltaj.impl.JavaVerbatimImpl <em>Java Verbatim</em>}' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see org.deltaj.deltaj.impl.JavaVerbatimImpl
   * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getJavaVerbatim()
   * @generated
   */
  int JAVA_VERBATIM = 61;

  /**
   * The feature id for the '<em><b>Verbatim</b></em>' attribute.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int JAVA_VERBATIM__VERBATIM = STATEMENT_FEATURE_COUNT + 0;

  /**
   * The number of structural features of the '<em>Java Verbatim</em>' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int JAVA_VERBATIM_FEATURE_COUNT = STATEMENT_FEATURE_COUNT + 1;

  /**
   * The meta object id for the '{@link org.deltaj.deltaj.impl.PlusImpl <em>Plus</em>}' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see org.deltaj.deltaj.impl.PlusImpl
   * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getPlus()
   * @generated
   */
  int PLUS = 62;

  /**
   * The feature id for the '<em><b>Left</b></em>' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int PLUS__LEFT = EXPRESSION_FEATURE_COUNT + 0;

  /**
   * The feature id for the '<em><b>Right</b></em>' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int PLUS__RIGHT = EXPRESSION_FEATURE_COUNT + 1;

  /**
   * The number of structural features of the '<em>Plus</em>' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int PLUS_FEATURE_COUNT = EXPRESSION_FEATURE_COUNT + 2;

  /**
   * The meta object id for the '{@link org.deltaj.deltaj.impl.MinusImpl <em>Minus</em>}' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see org.deltaj.deltaj.impl.MinusImpl
   * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getMinus()
   * @generated
   */
  int MINUS = 63;

  /**
   * The feature id for the '<em><b>Left</b></em>' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int MINUS__LEFT = EXPRESSION_FEATURE_COUNT + 0;

  /**
   * The feature id for the '<em><b>Right</b></em>' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int MINUS__RIGHT = EXPRESSION_FEATURE_COUNT + 1;

  /**
   * The number of structural features of the '<em>Minus</em>' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int MINUS_FEATURE_COUNT = EXPRESSION_FEATURE_COUNT + 2;

  /**
   * The meta object id for the '{@link org.deltaj.deltaj.impl.MultiOrDivImpl <em>Multi Or Div</em>}' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see org.deltaj.deltaj.impl.MultiOrDivImpl
   * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getMultiOrDiv()
   * @generated
   */
  int MULTI_OR_DIV = 64;

  /**
   * The feature id for the '<em><b>Left</b></em>' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int MULTI_OR_DIV__LEFT = EXPRESSION_FEATURE_COUNT + 0;

  /**
   * The feature id for the '<em><b>Op</b></em>' attribute.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int MULTI_OR_DIV__OP = EXPRESSION_FEATURE_COUNT + 1;

  /**
   * The feature id for the '<em><b>Right</b></em>' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int MULTI_OR_DIV__RIGHT = EXPRESSION_FEATURE_COUNT + 2;

  /**
   * The number of structural features of the '<em>Multi Or Div</em>' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int MULTI_OR_DIV_FEATURE_COUNT = EXPRESSION_FEATURE_COUNT + 3;

  /**
   * The meta object id for the '{@link org.deltaj.deltaj.impl.ComparisonImpl <em>Comparison</em>}' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see org.deltaj.deltaj.impl.ComparisonImpl
   * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getComparison()
   * @generated
   */
  int COMPARISON = 65;

  /**
   * The feature id for the '<em><b>Left</b></em>' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int COMPARISON__LEFT = EXPRESSION_FEATURE_COUNT + 0;

  /**
   * The feature id for the '<em><b>Op</b></em>' attribute.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int COMPARISON__OP = EXPRESSION_FEATURE_COUNT + 1;

  /**
   * The feature id for the '<em><b>Right</b></em>' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int COMPARISON__RIGHT = EXPRESSION_FEATURE_COUNT + 2;

  /**
   * The number of structural features of the '<em>Comparison</em>' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int COMPARISON_FEATURE_COUNT = EXPRESSION_FEATURE_COUNT + 3;

  /**
   * The meta object id for the '{@link org.deltaj.deltaj.impl.AndOrExpressionImpl <em>And Or Expression</em>}' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see org.deltaj.deltaj.impl.AndOrExpressionImpl
   * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getAndOrExpression()
   * @generated
   */
  int AND_OR_EXPRESSION = 66;

  /**
   * The feature id for the '<em><b>Left</b></em>' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int AND_OR_EXPRESSION__LEFT = EXPRESSION_FEATURE_COUNT + 0;

  /**
   * The feature id for the '<em><b>Op</b></em>' attribute.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int AND_OR_EXPRESSION__OP = EXPRESSION_FEATURE_COUNT + 1;

  /**
   * The feature id for the '<em><b>Right</b></em>' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int AND_OR_EXPRESSION__RIGHT = EXPRESSION_FEATURE_COUNT + 2;

  /**
   * The number of structural features of the '<em>And Or Expression</em>' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int AND_OR_EXPRESSION_FEATURE_COUNT = EXPRESSION_FEATURE_COUNT + 3;

  /**
   * The meta object id for the '{@link org.deltaj.deltaj.impl.BooleanNegationImpl <em>Boolean Negation</em>}' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see org.deltaj.deltaj.impl.BooleanNegationImpl
   * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getBooleanNegation()
   * @generated
   */
  int BOOLEAN_NEGATION = 67;

  /**
   * The feature id for the '<em><b>Expression</b></em>' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int BOOLEAN_NEGATION__EXPRESSION = EXPRESSION_FEATURE_COUNT + 0;

  /**
   * The number of structural features of the '<em>Boolean Negation</em>' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int BOOLEAN_NEGATION_FEATURE_COUNT = EXPRESSION_FEATURE_COUNT + 1;

  /**
   * The meta object id for the '{@link org.deltaj.deltaj.impl.ArithmeticSignedImpl <em>Arithmetic Signed</em>}' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see org.deltaj.deltaj.impl.ArithmeticSignedImpl
   * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getArithmeticSigned()
   * @generated
   */
  int ARITHMETIC_SIGNED = 68;

  /**
   * The feature id for the '<em><b>Expression</b></em>' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int ARITHMETIC_SIGNED__EXPRESSION = EXPRESSION_FEATURE_COUNT + 0;

  /**
   * The number of structural features of the '<em>Arithmetic Signed</em>' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int ARITHMETIC_SIGNED_FEATURE_COUNT = EXPRESSION_FEATURE_COUNT + 1;

  /**
   * The meta object id for the '{@link org.deltaj.deltaj.impl.SelectionImpl <em>Selection</em>}' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see org.deltaj.deltaj.impl.SelectionImpl
   * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getSelection()
   * @generated
   */
  int SELECTION = 69;

  /**
   * The feature id for the '<em><b>Receiver</b></em>' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int SELECTION__RECEIVER = EXPRESSION_FEATURE_COUNT + 0;

  /**
   * The feature id for the '<em><b>Message</b></em>' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int SELECTION__MESSAGE = EXPRESSION_FEATURE_COUNT + 1;

  /**
   * The number of structural features of the '<em>Selection</em>' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int SELECTION_FEATURE_COUNT = EXPRESSION_FEATURE_COUNT + 2;

  /**
   * The meta object id for the '{@link org.deltaj.deltaj.impl.OrImpl <em>Or</em>}' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see org.deltaj.deltaj.impl.OrImpl
   * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getOr()
   * @generated
   */
  int OR = 70;

  /**
   * The feature id for the '<em><b>Left</b></em>' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int OR__LEFT = PROPOSITIONAL_FORMULA_FEATURE_COUNT + 0;

  /**
   * The feature id for the '<em><b>Right</b></em>' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int OR__RIGHT = PROPOSITIONAL_FORMULA_FEATURE_COUNT + 1;

  /**
   * The number of structural features of the '<em>Or</em>' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int OR_FEATURE_COUNT = PROPOSITIONAL_FORMULA_FEATURE_COUNT + 2;

  /**
   * The meta object id for the '{@link org.deltaj.deltaj.impl.AndImpl <em>And</em>}' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see org.deltaj.deltaj.impl.AndImpl
   * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getAnd()
   * @generated
   */
  int AND = 71;

  /**
   * The feature id for the '<em><b>Left</b></em>' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int AND__LEFT = PROPOSITIONAL_FORMULA_FEATURE_COUNT + 0;

  /**
   * The feature id for the '<em><b>Right</b></em>' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int AND__RIGHT = PROPOSITIONAL_FORMULA_FEATURE_COUNT + 1;

  /**
   * The number of structural features of the '<em>And</em>' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int AND_FEATURE_COUNT = PROPOSITIONAL_FORMULA_FEATURE_COUNT + 2;

  /**
   * The meta object id for the '{@link org.deltaj.deltaj.impl.FeatureRefImpl <em>Feature Ref</em>}' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see org.deltaj.deltaj.impl.FeatureRefImpl
   * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getFeatureRef()
   * @generated
   */
  int FEATURE_REF = 72;

  /**
   * The feature id for the '<em><b>Feature</b></em>' reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int FEATURE_REF__FEATURE = PROPOSITIONAL_FORMULA_FEATURE_COUNT + 0;

  /**
   * The number of structural features of the '<em>Feature Ref</em>' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int FEATURE_REF_FEATURE_COUNT = PROPOSITIONAL_FORMULA_FEATURE_COUNT + 1;

  /**
   * The meta object id for the '{@link org.deltaj.deltaj.impl.PropParenImpl <em>Prop Paren</em>}' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see org.deltaj.deltaj.impl.PropParenImpl
   * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getPropParen()
   * @generated
   */
  int PROP_PAREN = 73;

  /**
   * The feature id for the '<em><b>Formula</b></em>' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int PROP_PAREN__FORMULA = PROPOSITIONAL_FORMULA_FEATURE_COUNT + 0;

  /**
   * The number of structural features of the '<em>Prop Paren</em>' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int PROP_PAREN_FEATURE_COUNT = PROPOSITIONAL_FORMULA_FEATURE_COUNT + 1;

  /**
   * The meta object id for the '{@link org.deltaj.deltaj.impl.NegationImpl <em>Negation</em>}' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see org.deltaj.deltaj.impl.NegationImpl
   * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getNegation()
   * @generated
   */
  int NEGATION = 74;

  /**
   * The feature id for the '<em><b>Formula</b></em>' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int NEGATION__FORMULA = PROPOSITIONAL_FORMULA_FEATURE_COUNT + 0;

  /**
   * The number of structural features of the '<em>Negation</em>' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int NEGATION_FEATURE_COUNT = PROPOSITIONAL_FORMULA_FEATURE_COUNT + 1;

  /**
   * The meta object id for the '{@link org.deltaj.deltaj.impl.PropTrueImpl <em>Prop True</em>}' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see org.deltaj.deltaj.impl.PropTrueImpl
   * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getPropTrue()
   * @generated
   */
  int PROP_TRUE = 75;

  /**
   * The number of structural features of the '<em>Prop True</em>' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int PROP_TRUE_FEATURE_COUNT = PROPOSITIONAL_FORMULA_FEATURE_COUNT + 0;

  /**
   * The meta object id for the '{@link org.deltaj.deltaj.impl.PropFalseImpl <em>Prop False</em>}' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see org.deltaj.deltaj.impl.PropFalseImpl
   * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getPropFalse()
   * @generated
   */
  int PROP_FALSE = 76;

  /**
   * The number of structural features of the '<em>Prop False</em>' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int PROP_FALSE_FEATURE_COUNT = PROPOSITIONAL_FORMULA_FEATURE_COUNT + 0;


  /**
   * Returns the meta object for class '{@link org.deltaj.deltaj.Program <em>Program</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for class '<em>Program</em>'.
   * @see org.deltaj.deltaj.Program
   * @generated
   */
  EClass getProgram();

  /**
   * Returns the meta object for the containment reference list '{@link org.deltaj.deltaj.Program#getDeltaModules <em>Delta Modules</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the containment reference list '<em>Delta Modules</em>'.
   * @see org.deltaj.deltaj.Program#getDeltaModules()
   * @see #getProgram()
   * @generated
   */
  EReference getProgram_DeltaModules();

  /**
   * Returns the meta object for the containment reference list '{@link org.deltaj.deltaj.Program#getProductLines <em>Product Lines</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the containment reference list '<em>Product Lines</em>'.
   * @see org.deltaj.deltaj.Program#getProductLines()
   * @see #getProgram()
   * @generated
   */
  EReference getProgram_ProductLines();

  /**
   * Returns the meta object for the containment reference list '{@link org.deltaj.deltaj.Program#getProducts <em>Products</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the containment reference list '<em>Products</em>'.
   * @see org.deltaj.deltaj.Program#getProducts()
   * @see #getProgram()
   * @generated
   */
  EReference getProgram_Products();

  /**
   * Returns the meta object for class '{@link org.deltaj.deltaj.Type <em>Type</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for class '<em>Type</em>'.
   * @see org.deltaj.deltaj.Type
   * @generated
   */
  EClass getType();

  /**
   * Returns the meta object for class '{@link org.deltaj.deltaj.TypeVariable <em>Type Variable</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for class '<em>Type Variable</em>'.
   * @see org.deltaj.deltaj.TypeVariable
   * @generated
   */
  EClass getTypeVariable();

  /**
   * Returns the meta object for the attribute '{@link org.deltaj.deltaj.TypeVariable#getVarName <em>Var Name</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the attribute '<em>Var Name</em>'.
   * @see org.deltaj.deltaj.TypeVariable#getVarName()
   * @see #getTypeVariable()
   * @generated
   */
  EAttribute getTypeVariable_VarName();

  /**
   * Returns the meta object for class '{@link org.deltaj.deltaj.TypeForMethod <em>Type For Method</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for class '<em>Type For Method</em>'.
   * @see org.deltaj.deltaj.TypeForMethod
   * @generated
   */
  EClass getTypeForMethod();

  /**
   * Returns the meta object for class '{@link org.deltaj.deltaj.VoidType <em>Void Type</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for class '<em>Void Type</em>'.
   * @see org.deltaj.deltaj.VoidType
   * @generated
   */
  EClass getVoidType();

  /**
   * Returns the meta object for the attribute '{@link org.deltaj.deltaj.VoidType#getVoid <em>Void</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the attribute '<em>Void</em>'.
   * @see org.deltaj.deltaj.VoidType#getVoid()
   * @see #getVoidType()
   * @generated
   */
  EAttribute getVoidType_Void();

  /**
   * Returns the meta object for class '{@link org.deltaj.deltaj.TypeForDeclaration <em>Type For Declaration</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for class '<em>Type For Declaration</em>'.
   * @see org.deltaj.deltaj.TypeForDeclaration
   * @generated
   */
  EClass getTypeForDeclaration();

  /**
   * Returns the meta object for class '{@link org.deltaj.deltaj.BasicType <em>Basic Type</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for class '<em>Basic Type</em>'.
   * @see org.deltaj.deltaj.BasicType
   * @generated
   */
  EClass getBasicType();

  /**
   * Returns the meta object for the attribute '{@link org.deltaj.deltaj.BasicType#getBasic <em>Basic</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the attribute '<em>Basic</em>'.
   * @see org.deltaj.deltaj.BasicType#getBasic()
   * @see #getBasicType()
   * @generated
   */
  EAttribute getBasicType_Basic();

  /**
   * Returns the meta object for class '{@link org.deltaj.deltaj.IntType <em>Int Type</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for class '<em>Int Type</em>'.
   * @see org.deltaj.deltaj.IntType
   * @generated
   */
  EClass getIntType();

  /**
   * Returns the meta object for class '{@link org.deltaj.deltaj.BooleanType <em>Boolean Type</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for class '<em>Boolean Type</em>'.
   * @see org.deltaj.deltaj.BooleanType
   * @generated
   */
  EClass getBooleanType();

  /**
   * Returns the meta object for class '{@link org.deltaj.deltaj.StringType <em>String Type</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for class '<em>String Type</em>'.
   * @see org.deltaj.deltaj.StringType
   * @generated
   */
  EClass getStringType();

  /**
   * Returns the meta object for class '{@link org.deltaj.deltaj.ClassType <em>Class Type</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for class '<em>Class Type</em>'.
   * @see org.deltaj.deltaj.ClassType
   * @generated
   */
  EClass getClassType();

  /**
   * Returns the meta object for the attribute '{@link org.deltaj.deltaj.ClassType#getClassref <em>Classref</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the attribute '<em>Classref</em>'.
   * @see org.deltaj.deltaj.ClassType#getClassref()
   * @see #getClassType()
   * @generated
   */
  EAttribute getClassType_Classref();

  /**
   * Returns the meta object for class '{@link org.deltaj.deltaj.Class <em>Class</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for class '<em>Class</em>'.
   * @see org.deltaj.deltaj.Class
   * @generated
   */
  EClass getClass_();

  /**
   * Returns the meta object for the attribute '{@link org.deltaj.deltaj.Class#getName <em>Name</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the attribute '<em>Name</em>'.
   * @see org.deltaj.deltaj.Class#getName()
   * @see #getClass_()
   * @generated
   */
  EAttribute getClass_Name();

  /**
   * Returns the meta object for the attribute '{@link org.deltaj.deltaj.Class#getExtends <em>Extends</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the attribute '<em>Extends</em>'.
   * @see org.deltaj.deltaj.Class#getExtends()
   * @see #getClass_()
   * @generated
   */
  EAttribute getClass_Extends();

  /**
   * Returns the meta object for the containment reference list '{@link org.deltaj.deltaj.Class#getFields <em>Fields</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the containment reference list '<em>Fields</em>'.
   * @see org.deltaj.deltaj.Class#getFields()
   * @see #getClass_()
   * @generated
   */
  EReference getClass_Fields();

  /**
   * Returns the meta object for the containment reference list '{@link org.deltaj.deltaj.Class#getMethods <em>Methods</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the containment reference list '<em>Methods</em>'.
   * @see org.deltaj.deltaj.Class#getMethods()
   * @see #getClass_()
   * @generated
   */
  EReference getClass_Methods();

  /**
   * Returns the meta object for class '{@link org.deltaj.deltaj.TypedDeclaration <em>Typed Declaration</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for class '<em>Typed Declaration</em>'.
   * @see org.deltaj.deltaj.TypedDeclaration
   * @generated
   */
  EClass getTypedDeclaration();

  /**
   * Returns the meta object for the containment reference '{@link org.deltaj.deltaj.TypedDeclaration#getType <em>Type</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the containment reference '<em>Type</em>'.
   * @see org.deltaj.deltaj.TypedDeclaration#getType()
   * @see #getTypedDeclaration()
   * @generated
   */
  EReference getTypedDeclaration_Type();

  /**
   * Returns the meta object for the attribute '{@link org.deltaj.deltaj.TypedDeclaration#getName <em>Name</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the attribute '<em>Name</em>'.
   * @see org.deltaj.deltaj.TypedDeclaration#getName()
   * @see #getTypedDeclaration()
   * @generated
   */
  EAttribute getTypedDeclaration_Name();

  /**
   * Returns the meta object for class '{@link org.deltaj.deltaj.Field <em>Field</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for class '<em>Field</em>'.
   * @see org.deltaj.deltaj.Field
   * @generated
   */
  EClass getField();

  /**
   * Returns the meta object for class '{@link org.deltaj.deltaj.LocalVariableDeclaration <em>Local Variable Declaration</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for class '<em>Local Variable Declaration</em>'.
   * @see org.deltaj.deltaj.LocalVariableDeclaration
   * @generated
   */
  EClass getLocalVariableDeclaration();

  /**
   * Returns the meta object for class '{@link org.deltaj.deltaj.Parameter <em>Parameter</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for class '<em>Parameter</em>'.
   * @see org.deltaj.deltaj.Parameter
   * @generated
   */
  EClass getParameter();

  /**
   * Returns the meta object for class '{@link org.deltaj.deltaj.Method <em>Method</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for class '<em>Method</em>'.
   * @see org.deltaj.deltaj.Method
   * @generated
   */
  EClass getMethod();

  /**
   * Returns the meta object for the containment reference '{@link org.deltaj.deltaj.Method#getReturntype <em>Returntype</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the containment reference '<em>Returntype</em>'.
   * @see org.deltaj.deltaj.Method#getReturntype()
   * @see #getMethod()
   * @generated
   */
  EReference getMethod_Returntype();

  /**
   * Returns the meta object for the attribute '{@link org.deltaj.deltaj.Method#getName <em>Name</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the attribute '<em>Name</em>'.
   * @see org.deltaj.deltaj.Method#getName()
   * @see #getMethod()
   * @generated
   */
  EAttribute getMethod_Name();

  /**
   * Returns the meta object for the containment reference list '{@link org.deltaj.deltaj.Method#getParams <em>Params</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the containment reference list '<em>Params</em>'.
   * @see org.deltaj.deltaj.Method#getParams()
   * @see #getMethod()
   * @generated
   */
  EReference getMethod_Params();

  /**
   * Returns the meta object for the containment reference '{@link org.deltaj.deltaj.Method#getBody <em>Body</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the containment reference '<em>Body</em>'.
   * @see org.deltaj.deltaj.Method#getBody()
   * @see #getMethod()
   * @generated
   */
  EReference getMethod_Body();

  /**
   * Returns the meta object for class '{@link org.deltaj.deltaj.StatementBlock <em>Statement Block</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for class '<em>Statement Block</em>'.
   * @see org.deltaj.deltaj.StatementBlock
   * @generated
   */
  EClass getStatementBlock();

  /**
   * Returns the meta object for the containment reference list '{@link org.deltaj.deltaj.StatementBlock#getLocalvariables <em>Localvariables</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the containment reference list '<em>Localvariables</em>'.
   * @see org.deltaj.deltaj.StatementBlock#getLocalvariables()
   * @see #getStatementBlock()
   * @generated
   */
  EReference getStatementBlock_Localvariables();

  /**
   * Returns the meta object for the containment reference list '{@link org.deltaj.deltaj.StatementBlock#getStatements <em>Statements</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the containment reference list '<em>Statements</em>'.
   * @see org.deltaj.deltaj.StatementBlock#getStatements()
   * @see #getStatementBlock()
   * @generated
   */
  EReference getStatementBlock_Statements();

  /**
   * Returns the meta object for class '{@link org.deltaj.deltaj.Statement <em>Statement</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for class '<em>Statement</em>'.
   * @see org.deltaj.deltaj.Statement
   * @generated
   */
  EClass getStatement();

  /**
   * Returns the meta object for class '{@link org.deltaj.deltaj.ExpressionStatement <em>Expression Statement</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for class '<em>Expression Statement</em>'.
   * @see org.deltaj.deltaj.ExpressionStatement
   * @generated
   */
  EClass getExpressionStatement();

  /**
   * Returns the meta object for the containment reference '{@link org.deltaj.deltaj.ExpressionStatement#getExpression <em>Expression</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the containment reference '<em>Expression</em>'.
   * @see org.deltaj.deltaj.ExpressionStatement#getExpression()
   * @see #getExpressionStatement()
   * @generated
   */
  EReference getExpressionStatement_Expression();

  /**
   * Returns the meta object for class '{@link org.deltaj.deltaj.Assignment <em>Assignment</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for class '<em>Assignment</em>'.
   * @see org.deltaj.deltaj.Assignment
   * @generated
   */
  EClass getAssignment();

  /**
   * Returns the meta object for the containment reference '{@link org.deltaj.deltaj.Assignment#getLeft <em>Left</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the containment reference '<em>Left</em>'.
   * @see org.deltaj.deltaj.Assignment#getLeft()
   * @see #getAssignment()
   * @generated
   */
  EReference getAssignment_Left();

  /**
   * Returns the meta object for the containment reference '{@link org.deltaj.deltaj.Assignment#getRight <em>Right</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the containment reference '<em>Right</em>'.
   * @see org.deltaj.deltaj.Assignment#getRight()
   * @see #getAssignment()
   * @generated
   */
  EReference getAssignment_Right();

  /**
   * Returns the meta object for class '{@link org.deltaj.deltaj.IfStatement <em>If Statement</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for class '<em>If Statement</em>'.
   * @see org.deltaj.deltaj.IfStatement
   * @generated
   */
  EClass getIfStatement();

  /**
   * Returns the meta object for the containment reference '{@link org.deltaj.deltaj.IfStatement#getExpression <em>Expression</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the containment reference '<em>Expression</em>'.
   * @see org.deltaj.deltaj.IfStatement#getExpression()
   * @see #getIfStatement()
   * @generated
   */
  EReference getIfStatement_Expression();

  /**
   * Returns the meta object for the containment reference '{@link org.deltaj.deltaj.IfStatement#getThenBlock <em>Then Block</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the containment reference '<em>Then Block</em>'.
   * @see org.deltaj.deltaj.IfStatement#getThenBlock()
   * @see #getIfStatement()
   * @generated
   */
  EReference getIfStatement_ThenBlock();

  /**
   * Returns the meta object for the containment reference '{@link org.deltaj.deltaj.IfStatement#getElseBlock <em>Else Block</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the containment reference '<em>Else Block</em>'.
   * @see org.deltaj.deltaj.IfStatement#getElseBlock()
   * @see #getIfStatement()
   * @generated
   */
  EReference getIfStatement_ElseBlock();

  /**
   * Returns the meta object for class '{@link org.deltaj.deltaj.Expression <em>Expression</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for class '<em>Expression</em>'.
   * @see org.deltaj.deltaj.Expression
   * @generated
   */
  EClass getExpression();

  /**
   * Returns the meta object for class '{@link org.deltaj.deltaj.Null <em>Null</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for class '<em>Null</em>'.
   * @see org.deltaj.deltaj.Null
   * @generated
   */
  EClass getNull();

  /**
   * Returns the meta object for the attribute '{@link org.deltaj.deltaj.Null#getNull <em>Null</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the attribute '<em>Null</em>'.
   * @see org.deltaj.deltaj.Null#getNull()
   * @see #getNull()
   * @generated
   */
  EAttribute getNull_Null();

  /**
   * Returns the meta object for class '{@link org.deltaj.deltaj.This <em>This</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for class '<em>This</em>'.
   * @see org.deltaj.deltaj.This
   * @generated
   */
  EClass getThis();

  /**
   * Returns the meta object for the attribute '{@link org.deltaj.deltaj.This#getVariable <em>Variable</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the attribute '<em>Variable</em>'.
   * @see org.deltaj.deltaj.This#getVariable()
   * @see #getThis()
   * @generated
   */
  EAttribute getThis_Variable();

  /**
   * Returns the meta object for class '{@link org.deltaj.deltaj.Original <em>Original</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for class '<em>Original</em>'.
   * @see org.deltaj.deltaj.Original
   * @generated
   */
  EClass getOriginal();

  /**
   * Returns the meta object for the attribute '{@link org.deltaj.deltaj.Original#getMethod <em>Method</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the attribute '<em>Method</em>'.
   * @see org.deltaj.deltaj.Original#getMethod()
   * @see #getOriginal()
   * @generated
   */
  EAttribute getOriginal_Method();

  /**
   * Returns the meta object for the containment reference list '{@link org.deltaj.deltaj.Original#getArgs <em>Args</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the containment reference list '<em>Args</em>'.
   * @see org.deltaj.deltaj.Original#getArgs()
   * @see #getOriginal()
   * @generated
   */
  EReference getOriginal_Args();

  /**
   * Returns the meta object for class '{@link org.deltaj.deltaj.VariableAccess <em>Variable Access</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for class '<em>Variable Access</em>'.
   * @see org.deltaj.deltaj.VariableAccess
   * @generated
   */
  EClass getVariableAccess();

  /**
   * Returns the meta object for the reference '{@link org.deltaj.deltaj.VariableAccess#getVariable <em>Variable</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the reference '<em>Variable</em>'.
   * @see org.deltaj.deltaj.VariableAccess#getVariable()
   * @see #getVariableAccess()
   * @generated
   */
  EReference getVariableAccess_Variable();

  /**
   * Returns the meta object for class '{@link org.deltaj.deltaj.New <em>New</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for class '<em>New</em>'.
   * @see org.deltaj.deltaj.New
   * @generated
   */
  EClass getNew();

  /**
   * Returns the meta object for the attribute '{@link org.deltaj.deltaj.New#getClass_ <em>Class</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the attribute '<em>Class</em>'.
   * @see org.deltaj.deltaj.New#getClass_()
   * @see #getNew()
   * @generated
   */
  EAttribute getNew_Class();

  /**
   * Returns the meta object for class '{@link org.deltaj.deltaj.Cast <em>Cast</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for class '<em>Cast</em>'.
   * @see org.deltaj.deltaj.Cast
   * @generated
   */
  EClass getCast();

  /**
   * Returns the meta object for the attribute '{@link org.deltaj.deltaj.Cast#getType <em>Type</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the attribute '<em>Type</em>'.
   * @see org.deltaj.deltaj.Cast#getType()
   * @see #getCast()
   * @generated
   */
  EAttribute getCast_Type();

  /**
   * Returns the meta object for the containment reference '{@link org.deltaj.deltaj.Cast#getObject <em>Object</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the containment reference '<em>Object</em>'.
   * @see org.deltaj.deltaj.Cast#getObject()
   * @see #getCast()
   * @generated
   */
  EReference getCast_Object();

  /**
   * Returns the meta object for class '{@link org.deltaj.deltaj.Paren <em>Paren</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for class '<em>Paren</em>'.
   * @see org.deltaj.deltaj.Paren
   * @generated
   */
  EClass getParen();

  /**
   * Returns the meta object for the containment reference '{@link org.deltaj.deltaj.Paren#getExpression <em>Expression</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the containment reference '<em>Expression</em>'.
   * @see org.deltaj.deltaj.Paren#getExpression()
   * @see #getParen()
   * @generated
   */
  EReference getParen_Expression();

  /**
   * Returns the meta object for class '{@link org.deltaj.deltaj.Constant <em>Constant</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for class '<em>Constant</em>'.
   * @see org.deltaj.deltaj.Constant
   * @generated
   */
  EClass getConstant();

  /**
   * Returns the meta object for class '{@link org.deltaj.deltaj.StringConstant <em>String Constant</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for class '<em>String Constant</em>'.
   * @see org.deltaj.deltaj.StringConstant
   * @generated
   */
  EClass getStringConstant();

  /**
   * Returns the meta object for the attribute '{@link org.deltaj.deltaj.StringConstant#getConstant <em>Constant</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the attribute '<em>Constant</em>'.
   * @see org.deltaj.deltaj.StringConstant#getConstant()
   * @see #getStringConstant()
   * @generated
   */
  EAttribute getStringConstant_Constant();

  /**
   * Returns the meta object for class '{@link org.deltaj.deltaj.IntConstant <em>Int Constant</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for class '<em>Int Constant</em>'.
   * @see org.deltaj.deltaj.IntConstant
   * @generated
   */
  EClass getIntConstant();

  /**
   * Returns the meta object for the attribute '{@link org.deltaj.deltaj.IntConstant#getConstant <em>Constant</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the attribute '<em>Constant</em>'.
   * @see org.deltaj.deltaj.IntConstant#getConstant()
   * @see #getIntConstant()
   * @generated
   */
  EAttribute getIntConstant_Constant();

  /**
   * Returns the meta object for class '{@link org.deltaj.deltaj.BoolConstant <em>Bool Constant</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for class '<em>Bool Constant</em>'.
   * @see org.deltaj.deltaj.BoolConstant
   * @generated
   */
  EClass getBoolConstant();

  /**
   * Returns the meta object for the attribute '{@link org.deltaj.deltaj.BoolConstant#getConstant <em>Constant</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the attribute '<em>Constant</em>'.
   * @see org.deltaj.deltaj.BoolConstant#getConstant()
   * @see #getBoolConstant()
   * @generated
   */
  EAttribute getBoolConstant_Constant();

  /**
   * Returns the meta object for class '{@link org.deltaj.deltaj.Message <em>Message</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for class '<em>Message</em>'.
   * @see org.deltaj.deltaj.Message
   * @generated
   */
  EClass getMessage();

  /**
   * Returns the meta object for class '{@link org.deltaj.deltaj.MethodCall <em>Method Call</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for class '<em>Method Call</em>'.
   * @see org.deltaj.deltaj.MethodCall
   * @generated
   */
  EClass getMethodCall();

  /**
   * Returns the meta object for the attribute '{@link org.deltaj.deltaj.MethodCall#getMethod <em>Method</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the attribute '<em>Method</em>'.
   * @see org.deltaj.deltaj.MethodCall#getMethod()
   * @see #getMethodCall()
   * @generated
   */
  EAttribute getMethodCall_Method();

  /**
   * Returns the meta object for the containment reference list '{@link org.deltaj.deltaj.MethodCall#getArgs <em>Args</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the containment reference list '<em>Args</em>'.
   * @see org.deltaj.deltaj.MethodCall#getArgs()
   * @see #getMethodCall()
   * @generated
   */
  EReference getMethodCall_Args();

  /**
   * Returns the meta object for class '{@link org.deltaj.deltaj.FieldSelection <em>Field Selection</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for class '<em>Field Selection</em>'.
   * @see org.deltaj.deltaj.FieldSelection
   * @generated
   */
  EClass getFieldSelection();

  /**
   * Returns the meta object for the attribute '{@link org.deltaj.deltaj.FieldSelection#getField <em>Field</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the attribute '<em>Field</em>'.
   * @see org.deltaj.deltaj.FieldSelection#getField()
   * @see #getFieldSelection()
   * @generated
   */
  EAttribute getFieldSelection_Field();

  /**
   * Returns the meta object for class '{@link org.deltaj.deltaj.DeltaModule <em>Delta Module</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for class '<em>Delta Module</em>'.
   * @see org.deltaj.deltaj.DeltaModule
   * @generated
   */
  EClass getDeltaModule();

  /**
   * Returns the meta object for the attribute '{@link org.deltaj.deltaj.DeltaModule#getName <em>Name</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the attribute '<em>Name</em>'.
   * @see org.deltaj.deltaj.DeltaModule#getName()
   * @see #getDeltaModule()
   * @generated
   */
  EAttribute getDeltaModule_Name();

  /**
   * Returns the meta object for the containment reference list '{@link org.deltaj.deltaj.DeltaModule#getDeltaActions <em>Delta Actions</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the containment reference list '<em>Delta Actions</em>'.
   * @see org.deltaj.deltaj.DeltaModule#getDeltaActions()
   * @see #getDeltaModule()
   * @generated
   */
  EReference getDeltaModule_DeltaActions();

  /**
   * Returns the meta object for class '{@link org.deltaj.deltaj.DeltaAction <em>Delta Action</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for class '<em>Delta Action</em>'.
   * @see org.deltaj.deltaj.DeltaAction
   * @generated
   */
  EClass getDeltaAction();

  /**
   * Returns the meta object for class '{@link org.deltaj.deltaj.ClassAddition <em>Class Addition</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for class '<em>Class Addition</em>'.
   * @see org.deltaj.deltaj.ClassAddition
   * @generated
   */
  EClass getClassAddition();

  /**
   * Returns the meta object for the containment reference '{@link org.deltaj.deltaj.ClassAddition#getClass_ <em>Class</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the containment reference '<em>Class</em>'.
   * @see org.deltaj.deltaj.ClassAddition#getClass_()
   * @see #getClassAddition()
   * @generated
   */
  EReference getClassAddition_Class();

  /**
   * Returns the meta object for class '{@link org.deltaj.deltaj.RemovesOrModifiesClass <em>Removes Or Modifies Class</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for class '<em>Removes Or Modifies Class</em>'.
   * @see org.deltaj.deltaj.RemovesOrModifiesClass
   * @generated
   */
  EClass getRemovesOrModifiesClass();

  /**
   * Returns the meta object for the attribute '{@link org.deltaj.deltaj.RemovesOrModifiesClass#getName <em>Name</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the attribute '<em>Name</em>'.
   * @see org.deltaj.deltaj.RemovesOrModifiesClass#getName()
   * @see #getRemovesOrModifiesClass()
   * @generated
   */
  EAttribute getRemovesOrModifiesClass_Name();

  /**
   * Returns the meta object for class '{@link org.deltaj.deltaj.ClassRemoval <em>Class Removal</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for class '<em>Class Removal</em>'.
   * @see org.deltaj.deltaj.ClassRemoval
   * @generated
   */
  EClass getClassRemoval();

  /**
   * Returns the meta object for class '{@link org.deltaj.deltaj.ClassModification <em>Class Modification</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for class '<em>Class Modification</em>'.
   * @see org.deltaj.deltaj.ClassModification
   * @generated
   */
  EClass getClassModification();

  /**
   * Returns the meta object for the attribute '{@link org.deltaj.deltaj.ClassModification#getExtends <em>Extends</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the attribute '<em>Extends</em>'.
   * @see org.deltaj.deltaj.ClassModification#getExtends()
   * @see #getClassModification()
   * @generated
   */
  EAttribute getClassModification_Extends();

  /**
   * Returns the meta object for the containment reference list '{@link org.deltaj.deltaj.ClassModification#getSubActions <em>Sub Actions</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the containment reference list '<em>Sub Actions</em>'.
   * @see org.deltaj.deltaj.ClassModification#getSubActions()
   * @see #getClassModification()
   * @generated
   */
  EReference getClassModification_SubActions();

  /**
   * Returns the meta object for class '{@link org.deltaj.deltaj.DeltaSubAction <em>Delta Sub Action</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for class '<em>Delta Sub Action</em>'.
   * @see org.deltaj.deltaj.DeltaSubAction
   * @generated
   */
  EClass getDeltaSubAction();

  /**
   * Returns the meta object for class '{@link org.deltaj.deltaj.MethodOrFieldAddition <em>Method Or Field Addition</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for class '<em>Method Or Field Addition</em>'.
   * @see org.deltaj.deltaj.MethodOrFieldAddition
   * @generated
   */
  EClass getMethodOrFieldAddition();

  /**
   * Returns the meta object for class '{@link org.deltaj.deltaj.FieldAddition <em>Field Addition</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for class '<em>Field Addition</em>'.
   * @see org.deltaj.deltaj.FieldAddition
   * @generated
   */
  EClass getFieldAddition();

  /**
   * Returns the meta object for the containment reference '{@link org.deltaj.deltaj.FieldAddition#getField <em>Field</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the containment reference '<em>Field</em>'.
   * @see org.deltaj.deltaj.FieldAddition#getField()
   * @see #getFieldAddition()
   * @generated
   */
  EReference getFieldAddition_Field();

  /**
   * Returns the meta object for class '{@link org.deltaj.deltaj.MethodAddition <em>Method Addition</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for class '<em>Method Addition</em>'.
   * @see org.deltaj.deltaj.MethodAddition
   * @generated
   */
  EClass getMethodAddition();

  /**
   * Returns the meta object for the containment reference '{@link org.deltaj.deltaj.MethodAddition#getMethod <em>Method</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the containment reference '<em>Method</em>'.
   * @see org.deltaj.deltaj.MethodAddition#getMethod()
   * @see #getMethodAddition()
   * @generated
   */
  EReference getMethodAddition_Method();

  /**
   * Returns the meta object for class '{@link org.deltaj.deltaj.FieldRemoval <em>Field Removal</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for class '<em>Field Removal</em>'.
   * @see org.deltaj.deltaj.FieldRemoval
   * @generated
   */
  EClass getFieldRemoval();

  /**
   * Returns the meta object for the attribute '{@link org.deltaj.deltaj.FieldRemoval#getName <em>Name</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the attribute '<em>Name</em>'.
   * @see org.deltaj.deltaj.FieldRemoval#getName()
   * @see #getFieldRemoval()
   * @generated
   */
  EAttribute getFieldRemoval_Name();

  /**
   * Returns the meta object for class '{@link org.deltaj.deltaj.MethodRemoval <em>Method Removal</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for class '<em>Method Removal</em>'.
   * @see org.deltaj.deltaj.MethodRemoval
   * @generated
   */
  EClass getMethodRemoval();

  /**
   * Returns the meta object for the attribute '{@link org.deltaj.deltaj.MethodRemoval#getName <em>Name</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the attribute '<em>Name</em>'.
   * @see org.deltaj.deltaj.MethodRemoval#getName()
   * @see #getMethodRemoval()
   * @generated
   */
  EAttribute getMethodRemoval_Name();

  /**
   * Returns the meta object for class '{@link org.deltaj.deltaj.MethodModification <em>Method Modification</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for class '<em>Method Modification</em>'.
   * @see org.deltaj.deltaj.MethodModification
   * @generated
   */
  EClass getMethodModification();

  /**
   * Returns the meta object for the containment reference '{@link org.deltaj.deltaj.MethodModification#getMethod <em>Method</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the containment reference '<em>Method</em>'.
   * @see org.deltaj.deltaj.MethodModification#getMethod()
   * @see #getMethodModification()
   * @generated
   */
  EReference getMethodModification_Method();

  /**
   * Returns the meta object for class '{@link org.deltaj.deltaj.ProductLine <em>Product Line</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for class '<em>Product Line</em>'.
   * @see org.deltaj.deltaj.ProductLine
   * @generated
   */
  EClass getProductLine();

  /**
   * Returns the meta object for the attribute '{@link org.deltaj.deltaj.ProductLine#getName <em>Name</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the attribute '<em>Name</em>'.
   * @see org.deltaj.deltaj.ProductLine#getName()
   * @see #getProductLine()
   * @generated
   */
  EAttribute getProductLine_Name();

  /**
   * Returns the meta object for the containment reference '{@link org.deltaj.deltaj.ProductLine#getFeatures <em>Features</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the containment reference '<em>Features</em>'.
   * @see org.deltaj.deltaj.ProductLine#getFeatures()
   * @see #getProductLine()
   * @generated
   */
  EReference getProductLine_Features();

  /**
   * Returns the meta object for the containment reference '{@link org.deltaj.deltaj.ProductLine#getConfigurations <em>Configurations</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the containment reference '<em>Configurations</em>'.
   * @see org.deltaj.deltaj.ProductLine#getConfigurations()
   * @see #getProductLine()
   * @generated
   */
  EReference getProductLine_Configurations();

  /**
   * Returns the meta object for the containment reference '{@link org.deltaj.deltaj.ProductLine#getPartition <em>Partition</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the containment reference '<em>Partition</em>'.
   * @see org.deltaj.deltaj.ProductLine#getPartition()
   * @see #getProductLine()
   * @generated
   */
  EReference getProductLine_Partition();

  /**
   * Returns the meta object for class '{@link org.deltaj.deltaj.Features <em>Features</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for class '<em>Features</em>'.
   * @see org.deltaj.deltaj.Features
   * @generated
   */
  EClass getFeatures();

  /**
   * Returns the meta object for the containment reference list '{@link org.deltaj.deltaj.Features#getFeaturesList <em>Features List</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the containment reference list '<em>Features List</em>'.
   * @see org.deltaj.deltaj.Features#getFeaturesList()
   * @see #getFeatures()
   * @generated
   */
  EReference getFeatures_FeaturesList();

  /**
   * Returns the meta object for class '{@link org.deltaj.deltaj.Feature <em>Feature</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for class '<em>Feature</em>'.
   * @see org.deltaj.deltaj.Feature
   * @generated
   */
  EClass getFeature();

  /**
   * Returns the meta object for the attribute '{@link org.deltaj.deltaj.Feature#getName <em>Name</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the attribute '<em>Name</em>'.
   * @see org.deltaj.deltaj.Feature#getName()
   * @see #getFeature()
   * @generated
   */
  EAttribute getFeature_Name();

  /**
   * Returns the meta object for class '{@link org.deltaj.deltaj.Configurations <em>Configurations</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for class '<em>Configurations</em>'.
   * @see org.deltaj.deltaj.Configurations
   * @generated
   */
  EClass getConfigurations();

  /**
   * Returns the meta object for the containment reference list '{@link org.deltaj.deltaj.Configurations#getConfigurations <em>Configurations</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the containment reference list '<em>Configurations</em>'.
   * @see org.deltaj.deltaj.Configurations#getConfigurations()
   * @see #getConfigurations()
   * @generated
   */
  EReference getConfigurations_Configurations();

  /**
   * Returns the meta object for class '{@link org.deltaj.deltaj.Configuration <em>Configuration</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for class '<em>Configuration</em>'.
   * @see org.deltaj.deltaj.Configuration
   * @generated
   */
  EClass getConfiguration();

  /**
   * Returns the meta object for the containment reference '{@link org.deltaj.deltaj.Configuration#getFormula <em>Formula</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the containment reference '<em>Formula</em>'.
   * @see org.deltaj.deltaj.Configuration#getFormula()
   * @see #getConfiguration()
   * @generated
   */
  EReference getConfiguration_Formula();

  /**
   * Returns the meta object for class '{@link org.deltaj.deltaj.DeltaPartition <em>Delta Partition</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for class '<em>Delta Partition</em>'.
   * @see org.deltaj.deltaj.DeltaPartition
   * @generated
   */
  EClass getDeltaPartition();

  /**
   * Returns the meta object for the containment reference list '{@link org.deltaj.deltaj.DeltaPartition#getParts <em>Parts</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the containment reference list '<em>Parts</em>'.
   * @see org.deltaj.deltaj.DeltaPartition#getParts()
   * @see #getDeltaPartition()
   * @generated
   */
  EReference getDeltaPartition_Parts();

  /**
   * Returns the meta object for class '{@link org.deltaj.deltaj.PartitionPart <em>Partition Part</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for class '<em>Partition Part</em>'.
   * @see org.deltaj.deltaj.PartitionPart
   * @generated
   */
  EClass getPartitionPart();

  /**
   * Returns the meta object for the containment reference list '{@link org.deltaj.deltaj.PartitionPart#getModuleReferences <em>Module References</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the containment reference list '<em>Module References</em>'.
   * @see org.deltaj.deltaj.PartitionPart#getModuleReferences()
   * @see #getPartitionPart()
   * @generated
   */
  EReference getPartitionPart_ModuleReferences();

  /**
   * Returns the meta object for class '{@link org.deltaj.deltaj.ModuleReference <em>Module Reference</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for class '<em>Module Reference</em>'.
   * @see org.deltaj.deltaj.ModuleReference
   * @generated
   */
  EClass getModuleReference();

  /**
   * Returns the meta object for the reference '{@link org.deltaj.deltaj.ModuleReference#getDeltaModule <em>Delta Module</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the reference '<em>Delta Module</em>'.
   * @see org.deltaj.deltaj.ModuleReference#getDeltaModule()
   * @see #getModuleReference()
   * @generated
   */
  EReference getModuleReference_DeltaModule();

  /**
   * Returns the meta object for the containment reference '{@link org.deltaj.deltaj.ModuleReference#getWhen <em>When</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the containment reference '<em>When</em>'.
   * @see org.deltaj.deltaj.ModuleReference#getWhen()
   * @see #getModuleReference()
   * @generated
   */
  EReference getModuleReference_When();

  /**
   * Returns the meta object for class '{@link org.deltaj.deltaj.PropositionalFormula <em>Propositional Formula</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for class '<em>Propositional Formula</em>'.
   * @see org.deltaj.deltaj.PropositionalFormula
   * @generated
   */
  EClass getPropositionalFormula();

  /**
   * Returns the meta object for class '{@link org.deltaj.deltaj.Product <em>Product</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for class '<em>Product</em>'.
   * @see org.deltaj.deltaj.Product
   * @generated
   */
  EClass getProduct();

  /**
   * Returns the meta object for the attribute '{@link org.deltaj.deltaj.Product#getName <em>Name</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the attribute '<em>Name</em>'.
   * @see org.deltaj.deltaj.Product#getName()
   * @see #getProduct()
   * @generated
   */
  EAttribute getProduct_Name();

  /**
   * Returns the meta object for the reference '{@link org.deltaj.deltaj.Product#getProductLine <em>Product Line</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the reference '<em>Product Line</em>'.
   * @see org.deltaj.deltaj.Product#getProductLine()
   * @see #getProduct()
   * @generated
   */
  EReference getProduct_ProductLine();

  /**
   * Returns the meta object for the reference list '{@link org.deltaj.deltaj.Product#getFeatures <em>Features</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the reference list '<em>Features</em>'.
   * @see org.deltaj.deltaj.Product#getFeatures()
   * @see #getProduct()
   * @generated
   */
  EReference getProduct_Features();

  /**
   * Returns the meta object for class '{@link org.deltaj.deltaj.ReturnStatement <em>Return Statement</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for class '<em>Return Statement</em>'.
   * @see org.deltaj.deltaj.ReturnStatement
   * @generated
   */
  EClass getReturnStatement();

  /**
   * Returns the meta object for the containment reference '{@link org.deltaj.deltaj.ReturnStatement#getExpression <em>Expression</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the containment reference '<em>Expression</em>'.
   * @see org.deltaj.deltaj.ReturnStatement#getExpression()
   * @see #getReturnStatement()
   * @generated
   */
  EReference getReturnStatement_Expression();

  /**
   * Returns the meta object for class '{@link org.deltaj.deltaj.JavaVerbatim <em>Java Verbatim</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for class '<em>Java Verbatim</em>'.
   * @see org.deltaj.deltaj.JavaVerbatim
   * @generated
   */
  EClass getJavaVerbatim();

  /**
   * Returns the meta object for the attribute '{@link org.deltaj.deltaj.JavaVerbatim#getVerbatim <em>Verbatim</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the attribute '<em>Verbatim</em>'.
   * @see org.deltaj.deltaj.JavaVerbatim#getVerbatim()
   * @see #getJavaVerbatim()
   * @generated
   */
  EAttribute getJavaVerbatim_Verbatim();

  /**
   * Returns the meta object for class '{@link org.deltaj.deltaj.Plus <em>Plus</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for class '<em>Plus</em>'.
   * @see org.deltaj.deltaj.Plus
   * @generated
   */
  EClass getPlus();

  /**
   * Returns the meta object for the containment reference '{@link org.deltaj.deltaj.Plus#getLeft <em>Left</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the containment reference '<em>Left</em>'.
   * @see org.deltaj.deltaj.Plus#getLeft()
   * @see #getPlus()
   * @generated
   */
  EReference getPlus_Left();

  /**
   * Returns the meta object for the containment reference '{@link org.deltaj.deltaj.Plus#getRight <em>Right</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the containment reference '<em>Right</em>'.
   * @see org.deltaj.deltaj.Plus#getRight()
   * @see #getPlus()
   * @generated
   */
  EReference getPlus_Right();

  /**
   * Returns the meta object for class '{@link org.deltaj.deltaj.Minus <em>Minus</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for class '<em>Minus</em>'.
   * @see org.deltaj.deltaj.Minus
   * @generated
   */
  EClass getMinus();

  /**
   * Returns the meta object for the containment reference '{@link org.deltaj.deltaj.Minus#getLeft <em>Left</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the containment reference '<em>Left</em>'.
   * @see org.deltaj.deltaj.Minus#getLeft()
   * @see #getMinus()
   * @generated
   */
  EReference getMinus_Left();

  /**
   * Returns the meta object for the containment reference '{@link org.deltaj.deltaj.Minus#getRight <em>Right</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the containment reference '<em>Right</em>'.
   * @see org.deltaj.deltaj.Minus#getRight()
   * @see #getMinus()
   * @generated
   */
  EReference getMinus_Right();

  /**
   * Returns the meta object for class '{@link org.deltaj.deltaj.MultiOrDiv <em>Multi Or Div</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for class '<em>Multi Or Div</em>'.
   * @see org.deltaj.deltaj.MultiOrDiv
   * @generated
   */
  EClass getMultiOrDiv();

  /**
   * Returns the meta object for the containment reference '{@link org.deltaj.deltaj.MultiOrDiv#getLeft <em>Left</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the containment reference '<em>Left</em>'.
   * @see org.deltaj.deltaj.MultiOrDiv#getLeft()
   * @see #getMultiOrDiv()
   * @generated
   */
  EReference getMultiOrDiv_Left();

  /**
   * Returns the meta object for the attribute '{@link org.deltaj.deltaj.MultiOrDiv#getOp <em>Op</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the attribute '<em>Op</em>'.
   * @see org.deltaj.deltaj.MultiOrDiv#getOp()
   * @see #getMultiOrDiv()
   * @generated
   */
  EAttribute getMultiOrDiv_Op();

  /**
   * Returns the meta object for the containment reference '{@link org.deltaj.deltaj.MultiOrDiv#getRight <em>Right</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the containment reference '<em>Right</em>'.
   * @see org.deltaj.deltaj.MultiOrDiv#getRight()
   * @see #getMultiOrDiv()
   * @generated
   */
  EReference getMultiOrDiv_Right();

  /**
   * Returns the meta object for class '{@link org.deltaj.deltaj.Comparison <em>Comparison</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for class '<em>Comparison</em>'.
   * @see org.deltaj.deltaj.Comparison
   * @generated
   */
  EClass getComparison();

  /**
   * Returns the meta object for the containment reference '{@link org.deltaj.deltaj.Comparison#getLeft <em>Left</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the containment reference '<em>Left</em>'.
   * @see org.deltaj.deltaj.Comparison#getLeft()
   * @see #getComparison()
   * @generated
   */
  EReference getComparison_Left();

  /**
   * Returns the meta object for the attribute '{@link org.deltaj.deltaj.Comparison#getOp <em>Op</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the attribute '<em>Op</em>'.
   * @see org.deltaj.deltaj.Comparison#getOp()
   * @see #getComparison()
   * @generated
   */
  EAttribute getComparison_Op();

  /**
   * Returns the meta object for the containment reference '{@link org.deltaj.deltaj.Comparison#getRight <em>Right</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the containment reference '<em>Right</em>'.
   * @see org.deltaj.deltaj.Comparison#getRight()
   * @see #getComparison()
   * @generated
   */
  EReference getComparison_Right();

  /**
   * Returns the meta object for class '{@link org.deltaj.deltaj.AndOrExpression <em>And Or Expression</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for class '<em>And Or Expression</em>'.
   * @see org.deltaj.deltaj.AndOrExpression
   * @generated
   */
  EClass getAndOrExpression();

  /**
   * Returns the meta object for the containment reference '{@link org.deltaj.deltaj.AndOrExpression#getLeft <em>Left</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the containment reference '<em>Left</em>'.
   * @see org.deltaj.deltaj.AndOrExpression#getLeft()
   * @see #getAndOrExpression()
   * @generated
   */
  EReference getAndOrExpression_Left();

  /**
   * Returns the meta object for the attribute '{@link org.deltaj.deltaj.AndOrExpression#getOp <em>Op</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the attribute '<em>Op</em>'.
   * @see org.deltaj.deltaj.AndOrExpression#getOp()
   * @see #getAndOrExpression()
   * @generated
   */
  EAttribute getAndOrExpression_Op();

  /**
   * Returns the meta object for the containment reference '{@link org.deltaj.deltaj.AndOrExpression#getRight <em>Right</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the containment reference '<em>Right</em>'.
   * @see org.deltaj.deltaj.AndOrExpression#getRight()
   * @see #getAndOrExpression()
   * @generated
   */
  EReference getAndOrExpression_Right();

  /**
   * Returns the meta object for class '{@link org.deltaj.deltaj.BooleanNegation <em>Boolean Negation</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for class '<em>Boolean Negation</em>'.
   * @see org.deltaj.deltaj.BooleanNegation
   * @generated
   */
  EClass getBooleanNegation();

  /**
   * Returns the meta object for the containment reference '{@link org.deltaj.deltaj.BooleanNegation#getExpression <em>Expression</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the containment reference '<em>Expression</em>'.
   * @see org.deltaj.deltaj.BooleanNegation#getExpression()
   * @see #getBooleanNegation()
   * @generated
   */
  EReference getBooleanNegation_Expression();

  /**
   * Returns the meta object for class '{@link org.deltaj.deltaj.ArithmeticSigned <em>Arithmetic Signed</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for class '<em>Arithmetic Signed</em>'.
   * @see org.deltaj.deltaj.ArithmeticSigned
   * @generated
   */
  EClass getArithmeticSigned();

  /**
   * Returns the meta object for the containment reference '{@link org.deltaj.deltaj.ArithmeticSigned#getExpression <em>Expression</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the containment reference '<em>Expression</em>'.
   * @see org.deltaj.deltaj.ArithmeticSigned#getExpression()
   * @see #getArithmeticSigned()
   * @generated
   */
  EReference getArithmeticSigned_Expression();

  /**
   * Returns the meta object for class '{@link org.deltaj.deltaj.Selection <em>Selection</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for class '<em>Selection</em>'.
   * @see org.deltaj.deltaj.Selection
   * @generated
   */
  EClass getSelection();

  /**
   * Returns the meta object for the containment reference '{@link org.deltaj.deltaj.Selection#getReceiver <em>Receiver</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the containment reference '<em>Receiver</em>'.
   * @see org.deltaj.deltaj.Selection#getReceiver()
   * @see #getSelection()
   * @generated
   */
  EReference getSelection_Receiver();

  /**
   * Returns the meta object for the containment reference '{@link org.deltaj.deltaj.Selection#getMessage <em>Message</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the containment reference '<em>Message</em>'.
   * @see org.deltaj.deltaj.Selection#getMessage()
   * @see #getSelection()
   * @generated
   */
  EReference getSelection_Message();

  /**
   * Returns the meta object for class '{@link org.deltaj.deltaj.Or <em>Or</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for class '<em>Or</em>'.
   * @see org.deltaj.deltaj.Or
   * @generated
   */
  EClass getOr();

  /**
   * Returns the meta object for the containment reference '{@link org.deltaj.deltaj.Or#getLeft <em>Left</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the containment reference '<em>Left</em>'.
   * @see org.deltaj.deltaj.Or#getLeft()
   * @see #getOr()
   * @generated
   */
  EReference getOr_Left();

  /**
   * Returns the meta object for the containment reference '{@link org.deltaj.deltaj.Or#getRight <em>Right</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the containment reference '<em>Right</em>'.
   * @see org.deltaj.deltaj.Or#getRight()
   * @see #getOr()
   * @generated
   */
  EReference getOr_Right();

  /**
   * Returns the meta object for class '{@link org.deltaj.deltaj.And <em>And</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for class '<em>And</em>'.
   * @see org.deltaj.deltaj.And
   * @generated
   */
  EClass getAnd();

  /**
   * Returns the meta object for the containment reference '{@link org.deltaj.deltaj.And#getLeft <em>Left</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the containment reference '<em>Left</em>'.
   * @see org.deltaj.deltaj.And#getLeft()
   * @see #getAnd()
   * @generated
   */
  EReference getAnd_Left();

  /**
   * Returns the meta object for the containment reference '{@link org.deltaj.deltaj.And#getRight <em>Right</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the containment reference '<em>Right</em>'.
   * @see org.deltaj.deltaj.And#getRight()
   * @see #getAnd()
   * @generated
   */
  EReference getAnd_Right();

  /**
   * Returns the meta object for class '{@link org.deltaj.deltaj.FeatureRef <em>Feature Ref</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for class '<em>Feature Ref</em>'.
   * @see org.deltaj.deltaj.FeatureRef
   * @generated
   */
  EClass getFeatureRef();

  /**
   * Returns the meta object for the reference '{@link org.deltaj.deltaj.FeatureRef#getFeature <em>Feature</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the reference '<em>Feature</em>'.
   * @see org.deltaj.deltaj.FeatureRef#getFeature()
   * @see #getFeatureRef()
   * @generated
   */
  EReference getFeatureRef_Feature();

  /**
   * Returns the meta object for class '{@link org.deltaj.deltaj.PropParen <em>Prop Paren</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for class '<em>Prop Paren</em>'.
   * @see org.deltaj.deltaj.PropParen
   * @generated
   */
  EClass getPropParen();

  /**
   * Returns the meta object for the containment reference '{@link org.deltaj.deltaj.PropParen#getFormula <em>Formula</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the containment reference '<em>Formula</em>'.
   * @see org.deltaj.deltaj.PropParen#getFormula()
   * @see #getPropParen()
   * @generated
   */
  EReference getPropParen_Formula();

  /**
   * Returns the meta object for class '{@link org.deltaj.deltaj.Negation <em>Negation</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for class '<em>Negation</em>'.
   * @see org.deltaj.deltaj.Negation
   * @generated
   */
  EClass getNegation();

  /**
   * Returns the meta object for the containment reference '{@link org.deltaj.deltaj.Negation#getFormula <em>Formula</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the containment reference '<em>Formula</em>'.
   * @see org.deltaj.deltaj.Negation#getFormula()
   * @see #getNegation()
   * @generated
   */
  EReference getNegation_Formula();

  /**
   * Returns the meta object for class '{@link org.deltaj.deltaj.PropTrue <em>Prop True</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for class '<em>Prop True</em>'.
   * @see org.deltaj.deltaj.PropTrue
   * @generated
   */
  EClass getPropTrue();

  /**
   * Returns the meta object for class '{@link org.deltaj.deltaj.PropFalse <em>Prop False</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for class '<em>Prop False</em>'.
   * @see org.deltaj.deltaj.PropFalse
   * @generated
   */
  EClass getPropFalse();

  /**
   * Returns the factory that creates the instances of the model.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the factory that creates the instances of the model.
   * @generated
   */
  DeltajFactory getDeltajFactory();

  /**
   * <!-- begin-user-doc -->
   * Defines literals for the meta objects that represent
   * <ul>
   *   <li>each class,</li>
   *   <li>each feature of each class,</li>
   *   <li>each enum,</li>
   *   <li>and each data type</li>
   * </ul>
   * <!-- end-user-doc -->
   * @generated
   */
  interface Literals
  {
    /**
     * The meta object literal for the '{@link org.deltaj.deltaj.impl.ProgramImpl <em>Program</em>}' class.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @see org.deltaj.deltaj.impl.ProgramImpl
     * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getProgram()
     * @generated
     */
    EClass PROGRAM = eINSTANCE.getProgram();

    /**
     * The meta object literal for the '<em><b>Delta Modules</b></em>' containment reference list feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference PROGRAM__DELTA_MODULES = eINSTANCE.getProgram_DeltaModules();

    /**
     * The meta object literal for the '<em><b>Product Lines</b></em>' containment reference list feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference PROGRAM__PRODUCT_LINES = eINSTANCE.getProgram_ProductLines();

    /**
     * The meta object literal for the '<em><b>Products</b></em>' containment reference list feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference PROGRAM__PRODUCTS = eINSTANCE.getProgram_Products();

    /**
     * The meta object literal for the '{@link org.deltaj.deltaj.impl.TypeImpl <em>Type</em>}' class.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @see org.deltaj.deltaj.impl.TypeImpl
     * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getType()
     * @generated
     */
    EClass TYPE = eINSTANCE.getType();

    /**
     * The meta object literal for the '{@link org.deltaj.deltaj.impl.TypeVariableImpl <em>Type Variable</em>}' class.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @see org.deltaj.deltaj.impl.TypeVariableImpl
     * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getTypeVariable()
     * @generated
     */
    EClass TYPE_VARIABLE = eINSTANCE.getTypeVariable();

    /**
     * The meta object literal for the '<em><b>Var Name</b></em>' attribute feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EAttribute TYPE_VARIABLE__VAR_NAME = eINSTANCE.getTypeVariable_VarName();

    /**
     * The meta object literal for the '{@link org.deltaj.deltaj.impl.TypeForMethodImpl <em>Type For Method</em>}' class.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @see org.deltaj.deltaj.impl.TypeForMethodImpl
     * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getTypeForMethod()
     * @generated
     */
    EClass TYPE_FOR_METHOD = eINSTANCE.getTypeForMethod();

    /**
     * The meta object literal for the '{@link org.deltaj.deltaj.impl.VoidTypeImpl <em>Void Type</em>}' class.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @see org.deltaj.deltaj.impl.VoidTypeImpl
     * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getVoidType()
     * @generated
     */
    EClass VOID_TYPE = eINSTANCE.getVoidType();

    /**
     * The meta object literal for the '<em><b>Void</b></em>' attribute feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EAttribute VOID_TYPE__VOID = eINSTANCE.getVoidType_Void();

    /**
     * The meta object literal for the '{@link org.deltaj.deltaj.impl.TypeForDeclarationImpl <em>Type For Declaration</em>}' class.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @see org.deltaj.deltaj.impl.TypeForDeclarationImpl
     * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getTypeForDeclaration()
     * @generated
     */
    EClass TYPE_FOR_DECLARATION = eINSTANCE.getTypeForDeclaration();

    /**
     * The meta object literal for the '{@link org.deltaj.deltaj.impl.BasicTypeImpl <em>Basic Type</em>}' class.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @see org.deltaj.deltaj.impl.BasicTypeImpl
     * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getBasicType()
     * @generated
     */
    EClass BASIC_TYPE = eINSTANCE.getBasicType();

    /**
     * The meta object literal for the '<em><b>Basic</b></em>' attribute feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EAttribute BASIC_TYPE__BASIC = eINSTANCE.getBasicType_Basic();

    /**
     * The meta object literal for the '{@link org.deltaj.deltaj.impl.IntTypeImpl <em>Int Type</em>}' class.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @see org.deltaj.deltaj.impl.IntTypeImpl
     * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getIntType()
     * @generated
     */
    EClass INT_TYPE = eINSTANCE.getIntType();

    /**
     * The meta object literal for the '{@link org.deltaj.deltaj.impl.BooleanTypeImpl <em>Boolean Type</em>}' class.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @see org.deltaj.deltaj.impl.BooleanTypeImpl
     * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getBooleanType()
     * @generated
     */
    EClass BOOLEAN_TYPE = eINSTANCE.getBooleanType();

    /**
     * The meta object literal for the '{@link org.deltaj.deltaj.impl.StringTypeImpl <em>String Type</em>}' class.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @see org.deltaj.deltaj.impl.StringTypeImpl
     * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getStringType()
     * @generated
     */
    EClass STRING_TYPE = eINSTANCE.getStringType();

    /**
     * The meta object literal for the '{@link org.deltaj.deltaj.impl.ClassTypeImpl <em>Class Type</em>}' class.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @see org.deltaj.deltaj.impl.ClassTypeImpl
     * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getClassType()
     * @generated
     */
    EClass CLASS_TYPE = eINSTANCE.getClassType();

    /**
     * The meta object literal for the '<em><b>Classref</b></em>' attribute feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EAttribute CLASS_TYPE__CLASSREF = eINSTANCE.getClassType_Classref();

    /**
     * The meta object literal for the '{@link org.deltaj.deltaj.impl.ClassImpl <em>Class</em>}' class.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @see org.deltaj.deltaj.impl.ClassImpl
     * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getClass_()
     * @generated
     */
    EClass CLASS = eINSTANCE.getClass_();

    /**
     * The meta object literal for the '<em><b>Name</b></em>' attribute feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EAttribute CLASS__NAME = eINSTANCE.getClass_Name();

    /**
     * The meta object literal for the '<em><b>Extends</b></em>' attribute feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EAttribute CLASS__EXTENDS = eINSTANCE.getClass_Extends();

    /**
     * The meta object literal for the '<em><b>Fields</b></em>' containment reference list feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference CLASS__FIELDS = eINSTANCE.getClass_Fields();

    /**
     * The meta object literal for the '<em><b>Methods</b></em>' containment reference list feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference CLASS__METHODS = eINSTANCE.getClass_Methods();

    /**
     * The meta object literal for the '{@link org.deltaj.deltaj.impl.TypedDeclarationImpl <em>Typed Declaration</em>}' class.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @see org.deltaj.deltaj.impl.TypedDeclarationImpl
     * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getTypedDeclaration()
     * @generated
     */
    EClass TYPED_DECLARATION = eINSTANCE.getTypedDeclaration();

    /**
     * The meta object literal for the '<em><b>Type</b></em>' containment reference feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference TYPED_DECLARATION__TYPE = eINSTANCE.getTypedDeclaration_Type();

    /**
     * The meta object literal for the '<em><b>Name</b></em>' attribute feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EAttribute TYPED_DECLARATION__NAME = eINSTANCE.getTypedDeclaration_Name();

    /**
     * The meta object literal for the '{@link org.deltaj.deltaj.impl.FieldImpl <em>Field</em>}' class.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @see org.deltaj.deltaj.impl.FieldImpl
     * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getField()
     * @generated
     */
    EClass FIELD = eINSTANCE.getField();

    /**
     * The meta object literal for the '{@link org.deltaj.deltaj.impl.LocalVariableDeclarationImpl <em>Local Variable Declaration</em>}' class.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @see org.deltaj.deltaj.impl.LocalVariableDeclarationImpl
     * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getLocalVariableDeclaration()
     * @generated
     */
    EClass LOCAL_VARIABLE_DECLARATION = eINSTANCE.getLocalVariableDeclaration();

    /**
     * The meta object literal for the '{@link org.deltaj.deltaj.impl.ParameterImpl <em>Parameter</em>}' class.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @see org.deltaj.deltaj.impl.ParameterImpl
     * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getParameter()
     * @generated
     */
    EClass PARAMETER = eINSTANCE.getParameter();

    /**
     * The meta object literal for the '{@link org.deltaj.deltaj.impl.MethodImpl <em>Method</em>}' class.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @see org.deltaj.deltaj.impl.MethodImpl
     * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getMethod()
     * @generated
     */
    EClass METHOD = eINSTANCE.getMethod();

    /**
     * The meta object literal for the '<em><b>Returntype</b></em>' containment reference feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference METHOD__RETURNTYPE = eINSTANCE.getMethod_Returntype();

    /**
     * The meta object literal for the '<em><b>Name</b></em>' attribute feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EAttribute METHOD__NAME = eINSTANCE.getMethod_Name();

    /**
     * The meta object literal for the '<em><b>Params</b></em>' containment reference list feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference METHOD__PARAMS = eINSTANCE.getMethod_Params();

    /**
     * The meta object literal for the '<em><b>Body</b></em>' containment reference feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference METHOD__BODY = eINSTANCE.getMethod_Body();

    /**
     * The meta object literal for the '{@link org.deltaj.deltaj.impl.StatementBlockImpl <em>Statement Block</em>}' class.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @see org.deltaj.deltaj.impl.StatementBlockImpl
     * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getStatementBlock()
     * @generated
     */
    EClass STATEMENT_BLOCK = eINSTANCE.getStatementBlock();

    /**
     * The meta object literal for the '<em><b>Localvariables</b></em>' containment reference list feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference STATEMENT_BLOCK__LOCALVARIABLES = eINSTANCE.getStatementBlock_Localvariables();

    /**
     * The meta object literal for the '<em><b>Statements</b></em>' containment reference list feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference STATEMENT_BLOCK__STATEMENTS = eINSTANCE.getStatementBlock_Statements();

    /**
     * The meta object literal for the '{@link org.deltaj.deltaj.impl.StatementImpl <em>Statement</em>}' class.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @see org.deltaj.deltaj.impl.StatementImpl
     * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getStatement()
     * @generated
     */
    EClass STATEMENT = eINSTANCE.getStatement();

    /**
     * The meta object literal for the '{@link org.deltaj.deltaj.impl.ExpressionStatementImpl <em>Expression Statement</em>}' class.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @see org.deltaj.deltaj.impl.ExpressionStatementImpl
     * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getExpressionStatement()
     * @generated
     */
    EClass EXPRESSION_STATEMENT = eINSTANCE.getExpressionStatement();

    /**
     * The meta object literal for the '<em><b>Expression</b></em>' containment reference feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference EXPRESSION_STATEMENT__EXPRESSION = eINSTANCE.getExpressionStatement_Expression();

    /**
     * The meta object literal for the '{@link org.deltaj.deltaj.impl.AssignmentImpl <em>Assignment</em>}' class.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @see org.deltaj.deltaj.impl.AssignmentImpl
     * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getAssignment()
     * @generated
     */
    EClass ASSIGNMENT = eINSTANCE.getAssignment();

    /**
     * The meta object literal for the '<em><b>Left</b></em>' containment reference feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference ASSIGNMENT__LEFT = eINSTANCE.getAssignment_Left();

    /**
     * The meta object literal for the '<em><b>Right</b></em>' containment reference feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference ASSIGNMENT__RIGHT = eINSTANCE.getAssignment_Right();

    /**
     * The meta object literal for the '{@link org.deltaj.deltaj.impl.IfStatementImpl <em>If Statement</em>}' class.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @see org.deltaj.deltaj.impl.IfStatementImpl
     * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getIfStatement()
     * @generated
     */
    EClass IF_STATEMENT = eINSTANCE.getIfStatement();

    /**
     * The meta object literal for the '<em><b>Expression</b></em>' containment reference feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference IF_STATEMENT__EXPRESSION = eINSTANCE.getIfStatement_Expression();

    /**
     * The meta object literal for the '<em><b>Then Block</b></em>' containment reference feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference IF_STATEMENT__THEN_BLOCK = eINSTANCE.getIfStatement_ThenBlock();

    /**
     * The meta object literal for the '<em><b>Else Block</b></em>' containment reference feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference IF_STATEMENT__ELSE_BLOCK = eINSTANCE.getIfStatement_ElseBlock();

    /**
     * The meta object literal for the '{@link org.deltaj.deltaj.impl.ExpressionImpl <em>Expression</em>}' class.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @see org.deltaj.deltaj.impl.ExpressionImpl
     * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getExpression()
     * @generated
     */
    EClass EXPRESSION = eINSTANCE.getExpression();

    /**
     * The meta object literal for the '{@link org.deltaj.deltaj.impl.NullImpl <em>Null</em>}' class.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @see org.deltaj.deltaj.impl.NullImpl
     * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getNull()
     * @generated
     */
    EClass NULL = eINSTANCE.getNull();

    /**
     * The meta object literal for the '<em><b>Null</b></em>' attribute feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EAttribute NULL__NULL = eINSTANCE.getNull_Null();

    /**
     * The meta object literal for the '{@link org.deltaj.deltaj.impl.ThisImpl <em>This</em>}' class.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @see org.deltaj.deltaj.impl.ThisImpl
     * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getThis()
     * @generated
     */
    EClass THIS = eINSTANCE.getThis();

    /**
     * The meta object literal for the '<em><b>Variable</b></em>' attribute feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EAttribute THIS__VARIABLE = eINSTANCE.getThis_Variable();

    /**
     * The meta object literal for the '{@link org.deltaj.deltaj.impl.OriginalImpl <em>Original</em>}' class.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @see org.deltaj.deltaj.impl.OriginalImpl
     * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getOriginal()
     * @generated
     */
    EClass ORIGINAL = eINSTANCE.getOriginal();

    /**
     * The meta object literal for the '<em><b>Method</b></em>' attribute feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EAttribute ORIGINAL__METHOD = eINSTANCE.getOriginal_Method();

    /**
     * The meta object literal for the '<em><b>Args</b></em>' containment reference list feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference ORIGINAL__ARGS = eINSTANCE.getOriginal_Args();

    /**
     * The meta object literal for the '{@link org.deltaj.deltaj.impl.VariableAccessImpl <em>Variable Access</em>}' class.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @see org.deltaj.deltaj.impl.VariableAccessImpl
     * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getVariableAccess()
     * @generated
     */
    EClass VARIABLE_ACCESS = eINSTANCE.getVariableAccess();

    /**
     * The meta object literal for the '<em><b>Variable</b></em>' reference feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference VARIABLE_ACCESS__VARIABLE = eINSTANCE.getVariableAccess_Variable();

    /**
     * The meta object literal for the '{@link org.deltaj.deltaj.impl.NewImpl <em>New</em>}' class.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @see org.deltaj.deltaj.impl.NewImpl
     * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getNew()
     * @generated
     */
    EClass NEW = eINSTANCE.getNew();

    /**
     * The meta object literal for the '<em><b>Class</b></em>' attribute feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EAttribute NEW__CLASS = eINSTANCE.getNew_Class();

    /**
     * The meta object literal for the '{@link org.deltaj.deltaj.impl.CastImpl <em>Cast</em>}' class.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @see org.deltaj.deltaj.impl.CastImpl
     * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getCast()
     * @generated
     */
    EClass CAST = eINSTANCE.getCast();

    /**
     * The meta object literal for the '<em><b>Type</b></em>' attribute feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EAttribute CAST__TYPE = eINSTANCE.getCast_Type();

    /**
     * The meta object literal for the '<em><b>Object</b></em>' containment reference feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference CAST__OBJECT = eINSTANCE.getCast_Object();

    /**
     * The meta object literal for the '{@link org.deltaj.deltaj.impl.ParenImpl <em>Paren</em>}' class.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @see org.deltaj.deltaj.impl.ParenImpl
     * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getParen()
     * @generated
     */
    EClass PAREN = eINSTANCE.getParen();

    /**
     * The meta object literal for the '<em><b>Expression</b></em>' containment reference feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference PAREN__EXPRESSION = eINSTANCE.getParen_Expression();

    /**
     * The meta object literal for the '{@link org.deltaj.deltaj.impl.ConstantImpl <em>Constant</em>}' class.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @see org.deltaj.deltaj.impl.ConstantImpl
     * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getConstant()
     * @generated
     */
    EClass CONSTANT = eINSTANCE.getConstant();

    /**
     * The meta object literal for the '{@link org.deltaj.deltaj.impl.StringConstantImpl <em>String Constant</em>}' class.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @see org.deltaj.deltaj.impl.StringConstantImpl
     * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getStringConstant()
     * @generated
     */
    EClass STRING_CONSTANT = eINSTANCE.getStringConstant();

    /**
     * The meta object literal for the '<em><b>Constant</b></em>' attribute feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EAttribute STRING_CONSTANT__CONSTANT = eINSTANCE.getStringConstant_Constant();

    /**
     * The meta object literal for the '{@link org.deltaj.deltaj.impl.IntConstantImpl <em>Int Constant</em>}' class.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @see org.deltaj.deltaj.impl.IntConstantImpl
     * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getIntConstant()
     * @generated
     */
    EClass INT_CONSTANT = eINSTANCE.getIntConstant();

    /**
     * The meta object literal for the '<em><b>Constant</b></em>' attribute feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EAttribute INT_CONSTANT__CONSTANT = eINSTANCE.getIntConstant_Constant();

    /**
     * The meta object literal for the '{@link org.deltaj.deltaj.impl.BoolConstantImpl <em>Bool Constant</em>}' class.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @see org.deltaj.deltaj.impl.BoolConstantImpl
     * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getBoolConstant()
     * @generated
     */
    EClass BOOL_CONSTANT = eINSTANCE.getBoolConstant();

    /**
     * The meta object literal for the '<em><b>Constant</b></em>' attribute feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EAttribute BOOL_CONSTANT__CONSTANT = eINSTANCE.getBoolConstant_Constant();

    /**
     * The meta object literal for the '{@link org.deltaj.deltaj.impl.MessageImpl <em>Message</em>}' class.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @see org.deltaj.deltaj.impl.MessageImpl
     * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getMessage()
     * @generated
     */
    EClass MESSAGE = eINSTANCE.getMessage();

    /**
     * The meta object literal for the '{@link org.deltaj.deltaj.impl.MethodCallImpl <em>Method Call</em>}' class.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @see org.deltaj.deltaj.impl.MethodCallImpl
     * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getMethodCall()
     * @generated
     */
    EClass METHOD_CALL = eINSTANCE.getMethodCall();

    /**
     * The meta object literal for the '<em><b>Method</b></em>' attribute feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EAttribute METHOD_CALL__METHOD = eINSTANCE.getMethodCall_Method();

    /**
     * The meta object literal for the '<em><b>Args</b></em>' containment reference list feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference METHOD_CALL__ARGS = eINSTANCE.getMethodCall_Args();

    /**
     * The meta object literal for the '{@link org.deltaj.deltaj.impl.FieldSelectionImpl <em>Field Selection</em>}' class.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @see org.deltaj.deltaj.impl.FieldSelectionImpl
     * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getFieldSelection()
     * @generated
     */
    EClass FIELD_SELECTION = eINSTANCE.getFieldSelection();

    /**
     * The meta object literal for the '<em><b>Field</b></em>' attribute feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EAttribute FIELD_SELECTION__FIELD = eINSTANCE.getFieldSelection_Field();

    /**
     * The meta object literal for the '{@link org.deltaj.deltaj.impl.DeltaModuleImpl <em>Delta Module</em>}' class.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @see org.deltaj.deltaj.impl.DeltaModuleImpl
     * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getDeltaModule()
     * @generated
     */
    EClass DELTA_MODULE = eINSTANCE.getDeltaModule();

    /**
     * The meta object literal for the '<em><b>Name</b></em>' attribute feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EAttribute DELTA_MODULE__NAME = eINSTANCE.getDeltaModule_Name();

    /**
     * The meta object literal for the '<em><b>Delta Actions</b></em>' containment reference list feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference DELTA_MODULE__DELTA_ACTIONS = eINSTANCE.getDeltaModule_DeltaActions();

    /**
     * The meta object literal for the '{@link org.deltaj.deltaj.impl.DeltaActionImpl <em>Delta Action</em>}' class.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @see org.deltaj.deltaj.impl.DeltaActionImpl
     * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getDeltaAction()
     * @generated
     */
    EClass DELTA_ACTION = eINSTANCE.getDeltaAction();

    /**
     * The meta object literal for the '{@link org.deltaj.deltaj.impl.ClassAdditionImpl <em>Class Addition</em>}' class.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @see org.deltaj.deltaj.impl.ClassAdditionImpl
     * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getClassAddition()
     * @generated
     */
    EClass CLASS_ADDITION = eINSTANCE.getClassAddition();

    /**
     * The meta object literal for the '<em><b>Class</b></em>' containment reference feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference CLASS_ADDITION__CLASS = eINSTANCE.getClassAddition_Class();

    /**
     * The meta object literal for the '{@link org.deltaj.deltaj.impl.RemovesOrModifiesClassImpl <em>Removes Or Modifies Class</em>}' class.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @see org.deltaj.deltaj.impl.RemovesOrModifiesClassImpl
     * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getRemovesOrModifiesClass()
     * @generated
     */
    EClass REMOVES_OR_MODIFIES_CLASS = eINSTANCE.getRemovesOrModifiesClass();

    /**
     * The meta object literal for the '<em><b>Name</b></em>' attribute feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EAttribute REMOVES_OR_MODIFIES_CLASS__NAME = eINSTANCE.getRemovesOrModifiesClass_Name();

    /**
     * The meta object literal for the '{@link org.deltaj.deltaj.impl.ClassRemovalImpl <em>Class Removal</em>}' class.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @see org.deltaj.deltaj.impl.ClassRemovalImpl
     * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getClassRemoval()
     * @generated
     */
    EClass CLASS_REMOVAL = eINSTANCE.getClassRemoval();

    /**
     * The meta object literal for the '{@link org.deltaj.deltaj.impl.ClassModificationImpl <em>Class Modification</em>}' class.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @see org.deltaj.deltaj.impl.ClassModificationImpl
     * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getClassModification()
     * @generated
     */
    EClass CLASS_MODIFICATION = eINSTANCE.getClassModification();

    /**
     * The meta object literal for the '<em><b>Extends</b></em>' attribute feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EAttribute CLASS_MODIFICATION__EXTENDS = eINSTANCE.getClassModification_Extends();

    /**
     * The meta object literal for the '<em><b>Sub Actions</b></em>' containment reference list feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference CLASS_MODIFICATION__SUB_ACTIONS = eINSTANCE.getClassModification_SubActions();

    /**
     * The meta object literal for the '{@link org.deltaj.deltaj.impl.DeltaSubActionImpl <em>Delta Sub Action</em>}' class.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @see org.deltaj.deltaj.impl.DeltaSubActionImpl
     * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getDeltaSubAction()
     * @generated
     */
    EClass DELTA_SUB_ACTION = eINSTANCE.getDeltaSubAction();

    /**
     * The meta object literal for the '{@link org.deltaj.deltaj.impl.MethodOrFieldAdditionImpl <em>Method Or Field Addition</em>}' class.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @see org.deltaj.deltaj.impl.MethodOrFieldAdditionImpl
     * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getMethodOrFieldAddition()
     * @generated
     */
    EClass METHOD_OR_FIELD_ADDITION = eINSTANCE.getMethodOrFieldAddition();

    /**
     * The meta object literal for the '{@link org.deltaj.deltaj.impl.FieldAdditionImpl <em>Field Addition</em>}' class.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @see org.deltaj.deltaj.impl.FieldAdditionImpl
     * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getFieldAddition()
     * @generated
     */
    EClass FIELD_ADDITION = eINSTANCE.getFieldAddition();

    /**
     * The meta object literal for the '<em><b>Field</b></em>' containment reference feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference FIELD_ADDITION__FIELD = eINSTANCE.getFieldAddition_Field();

    /**
     * The meta object literal for the '{@link org.deltaj.deltaj.impl.MethodAdditionImpl <em>Method Addition</em>}' class.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @see org.deltaj.deltaj.impl.MethodAdditionImpl
     * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getMethodAddition()
     * @generated
     */
    EClass METHOD_ADDITION = eINSTANCE.getMethodAddition();

    /**
     * The meta object literal for the '<em><b>Method</b></em>' containment reference feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference METHOD_ADDITION__METHOD = eINSTANCE.getMethodAddition_Method();

    /**
     * The meta object literal for the '{@link org.deltaj.deltaj.impl.FieldRemovalImpl <em>Field Removal</em>}' class.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @see org.deltaj.deltaj.impl.FieldRemovalImpl
     * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getFieldRemoval()
     * @generated
     */
    EClass FIELD_REMOVAL = eINSTANCE.getFieldRemoval();

    /**
     * The meta object literal for the '<em><b>Name</b></em>' attribute feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EAttribute FIELD_REMOVAL__NAME = eINSTANCE.getFieldRemoval_Name();

    /**
     * The meta object literal for the '{@link org.deltaj.deltaj.impl.MethodRemovalImpl <em>Method Removal</em>}' class.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @see org.deltaj.deltaj.impl.MethodRemovalImpl
     * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getMethodRemoval()
     * @generated
     */
    EClass METHOD_REMOVAL = eINSTANCE.getMethodRemoval();

    /**
     * The meta object literal for the '<em><b>Name</b></em>' attribute feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EAttribute METHOD_REMOVAL__NAME = eINSTANCE.getMethodRemoval_Name();

    /**
     * The meta object literal for the '{@link org.deltaj.deltaj.impl.MethodModificationImpl <em>Method Modification</em>}' class.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @see org.deltaj.deltaj.impl.MethodModificationImpl
     * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getMethodModification()
     * @generated
     */
    EClass METHOD_MODIFICATION = eINSTANCE.getMethodModification();

    /**
     * The meta object literal for the '<em><b>Method</b></em>' containment reference feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference METHOD_MODIFICATION__METHOD = eINSTANCE.getMethodModification_Method();

    /**
     * The meta object literal for the '{@link org.deltaj.deltaj.impl.ProductLineImpl <em>Product Line</em>}' class.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @see org.deltaj.deltaj.impl.ProductLineImpl
     * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getProductLine()
     * @generated
     */
    EClass PRODUCT_LINE = eINSTANCE.getProductLine();

    /**
     * The meta object literal for the '<em><b>Name</b></em>' attribute feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EAttribute PRODUCT_LINE__NAME = eINSTANCE.getProductLine_Name();

    /**
     * The meta object literal for the '<em><b>Features</b></em>' containment reference feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference PRODUCT_LINE__FEATURES = eINSTANCE.getProductLine_Features();

    /**
     * The meta object literal for the '<em><b>Configurations</b></em>' containment reference feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference PRODUCT_LINE__CONFIGURATIONS = eINSTANCE.getProductLine_Configurations();

    /**
     * The meta object literal for the '<em><b>Partition</b></em>' containment reference feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference PRODUCT_LINE__PARTITION = eINSTANCE.getProductLine_Partition();

    /**
     * The meta object literal for the '{@link org.deltaj.deltaj.impl.FeaturesImpl <em>Features</em>}' class.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @see org.deltaj.deltaj.impl.FeaturesImpl
     * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getFeatures()
     * @generated
     */
    EClass FEATURES = eINSTANCE.getFeatures();

    /**
     * The meta object literal for the '<em><b>Features List</b></em>' containment reference list feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference FEATURES__FEATURES_LIST = eINSTANCE.getFeatures_FeaturesList();

    /**
     * The meta object literal for the '{@link org.deltaj.deltaj.impl.FeatureImpl <em>Feature</em>}' class.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @see org.deltaj.deltaj.impl.FeatureImpl
     * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getFeature()
     * @generated
     */
    EClass FEATURE = eINSTANCE.getFeature();

    /**
     * The meta object literal for the '<em><b>Name</b></em>' attribute feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EAttribute FEATURE__NAME = eINSTANCE.getFeature_Name();

    /**
     * The meta object literal for the '{@link org.deltaj.deltaj.impl.ConfigurationsImpl <em>Configurations</em>}' class.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @see org.deltaj.deltaj.impl.ConfigurationsImpl
     * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getConfigurations()
     * @generated
     */
    EClass CONFIGURATIONS = eINSTANCE.getConfigurations();

    /**
     * The meta object literal for the '<em><b>Configurations</b></em>' containment reference list feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference CONFIGURATIONS__CONFIGURATIONS = eINSTANCE.getConfigurations_Configurations();

    /**
     * The meta object literal for the '{@link org.deltaj.deltaj.impl.ConfigurationImpl <em>Configuration</em>}' class.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @see org.deltaj.deltaj.impl.ConfigurationImpl
     * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getConfiguration()
     * @generated
     */
    EClass CONFIGURATION = eINSTANCE.getConfiguration();

    /**
     * The meta object literal for the '<em><b>Formula</b></em>' containment reference feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference CONFIGURATION__FORMULA = eINSTANCE.getConfiguration_Formula();

    /**
     * The meta object literal for the '{@link org.deltaj.deltaj.impl.DeltaPartitionImpl <em>Delta Partition</em>}' class.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @see org.deltaj.deltaj.impl.DeltaPartitionImpl
     * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getDeltaPartition()
     * @generated
     */
    EClass DELTA_PARTITION = eINSTANCE.getDeltaPartition();

    /**
     * The meta object literal for the '<em><b>Parts</b></em>' containment reference list feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference DELTA_PARTITION__PARTS = eINSTANCE.getDeltaPartition_Parts();

    /**
     * The meta object literal for the '{@link org.deltaj.deltaj.impl.PartitionPartImpl <em>Partition Part</em>}' class.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @see org.deltaj.deltaj.impl.PartitionPartImpl
     * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getPartitionPart()
     * @generated
     */
    EClass PARTITION_PART = eINSTANCE.getPartitionPart();

    /**
     * The meta object literal for the '<em><b>Module References</b></em>' containment reference list feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference PARTITION_PART__MODULE_REFERENCES = eINSTANCE.getPartitionPart_ModuleReferences();

    /**
     * The meta object literal for the '{@link org.deltaj.deltaj.impl.ModuleReferenceImpl <em>Module Reference</em>}' class.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @see org.deltaj.deltaj.impl.ModuleReferenceImpl
     * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getModuleReference()
     * @generated
     */
    EClass MODULE_REFERENCE = eINSTANCE.getModuleReference();

    /**
     * The meta object literal for the '<em><b>Delta Module</b></em>' reference feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference MODULE_REFERENCE__DELTA_MODULE = eINSTANCE.getModuleReference_DeltaModule();

    /**
     * The meta object literal for the '<em><b>When</b></em>' containment reference feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference MODULE_REFERENCE__WHEN = eINSTANCE.getModuleReference_When();

    /**
     * The meta object literal for the '{@link org.deltaj.deltaj.impl.PropositionalFormulaImpl <em>Propositional Formula</em>}' class.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @see org.deltaj.deltaj.impl.PropositionalFormulaImpl
     * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getPropositionalFormula()
     * @generated
     */
    EClass PROPOSITIONAL_FORMULA = eINSTANCE.getPropositionalFormula();

    /**
     * The meta object literal for the '{@link org.deltaj.deltaj.impl.ProductImpl <em>Product</em>}' class.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @see org.deltaj.deltaj.impl.ProductImpl
     * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getProduct()
     * @generated
     */
    EClass PRODUCT = eINSTANCE.getProduct();

    /**
     * The meta object literal for the '<em><b>Name</b></em>' attribute feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EAttribute PRODUCT__NAME = eINSTANCE.getProduct_Name();

    /**
     * The meta object literal for the '<em><b>Product Line</b></em>' reference feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference PRODUCT__PRODUCT_LINE = eINSTANCE.getProduct_ProductLine();

    /**
     * The meta object literal for the '<em><b>Features</b></em>' reference list feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference PRODUCT__FEATURES = eINSTANCE.getProduct_Features();

    /**
     * The meta object literal for the '{@link org.deltaj.deltaj.impl.ReturnStatementImpl <em>Return Statement</em>}' class.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @see org.deltaj.deltaj.impl.ReturnStatementImpl
     * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getReturnStatement()
     * @generated
     */
    EClass RETURN_STATEMENT = eINSTANCE.getReturnStatement();

    /**
     * The meta object literal for the '<em><b>Expression</b></em>' containment reference feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference RETURN_STATEMENT__EXPRESSION = eINSTANCE.getReturnStatement_Expression();

    /**
     * The meta object literal for the '{@link org.deltaj.deltaj.impl.JavaVerbatimImpl <em>Java Verbatim</em>}' class.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @see org.deltaj.deltaj.impl.JavaVerbatimImpl
     * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getJavaVerbatim()
     * @generated
     */
    EClass JAVA_VERBATIM = eINSTANCE.getJavaVerbatim();

    /**
     * The meta object literal for the '<em><b>Verbatim</b></em>' attribute feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EAttribute JAVA_VERBATIM__VERBATIM = eINSTANCE.getJavaVerbatim_Verbatim();

    /**
     * The meta object literal for the '{@link org.deltaj.deltaj.impl.PlusImpl <em>Plus</em>}' class.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @see org.deltaj.deltaj.impl.PlusImpl
     * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getPlus()
     * @generated
     */
    EClass PLUS = eINSTANCE.getPlus();

    /**
     * The meta object literal for the '<em><b>Left</b></em>' containment reference feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference PLUS__LEFT = eINSTANCE.getPlus_Left();

    /**
     * The meta object literal for the '<em><b>Right</b></em>' containment reference feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference PLUS__RIGHT = eINSTANCE.getPlus_Right();

    /**
     * The meta object literal for the '{@link org.deltaj.deltaj.impl.MinusImpl <em>Minus</em>}' class.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @see org.deltaj.deltaj.impl.MinusImpl
     * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getMinus()
     * @generated
     */
    EClass MINUS = eINSTANCE.getMinus();

    /**
     * The meta object literal for the '<em><b>Left</b></em>' containment reference feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference MINUS__LEFT = eINSTANCE.getMinus_Left();

    /**
     * The meta object literal for the '<em><b>Right</b></em>' containment reference feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference MINUS__RIGHT = eINSTANCE.getMinus_Right();

    /**
     * The meta object literal for the '{@link org.deltaj.deltaj.impl.MultiOrDivImpl <em>Multi Or Div</em>}' class.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @see org.deltaj.deltaj.impl.MultiOrDivImpl
     * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getMultiOrDiv()
     * @generated
     */
    EClass MULTI_OR_DIV = eINSTANCE.getMultiOrDiv();

    /**
     * The meta object literal for the '<em><b>Left</b></em>' containment reference feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference MULTI_OR_DIV__LEFT = eINSTANCE.getMultiOrDiv_Left();

    /**
     * The meta object literal for the '<em><b>Op</b></em>' attribute feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EAttribute MULTI_OR_DIV__OP = eINSTANCE.getMultiOrDiv_Op();

    /**
     * The meta object literal for the '<em><b>Right</b></em>' containment reference feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference MULTI_OR_DIV__RIGHT = eINSTANCE.getMultiOrDiv_Right();

    /**
     * The meta object literal for the '{@link org.deltaj.deltaj.impl.ComparisonImpl <em>Comparison</em>}' class.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @see org.deltaj.deltaj.impl.ComparisonImpl
     * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getComparison()
     * @generated
     */
    EClass COMPARISON = eINSTANCE.getComparison();

    /**
     * The meta object literal for the '<em><b>Left</b></em>' containment reference feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference COMPARISON__LEFT = eINSTANCE.getComparison_Left();

    /**
     * The meta object literal for the '<em><b>Op</b></em>' attribute feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EAttribute COMPARISON__OP = eINSTANCE.getComparison_Op();

    /**
     * The meta object literal for the '<em><b>Right</b></em>' containment reference feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference COMPARISON__RIGHT = eINSTANCE.getComparison_Right();

    /**
     * The meta object literal for the '{@link org.deltaj.deltaj.impl.AndOrExpressionImpl <em>And Or Expression</em>}' class.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @see org.deltaj.deltaj.impl.AndOrExpressionImpl
     * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getAndOrExpression()
     * @generated
     */
    EClass AND_OR_EXPRESSION = eINSTANCE.getAndOrExpression();

    /**
     * The meta object literal for the '<em><b>Left</b></em>' containment reference feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference AND_OR_EXPRESSION__LEFT = eINSTANCE.getAndOrExpression_Left();

    /**
     * The meta object literal for the '<em><b>Op</b></em>' attribute feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EAttribute AND_OR_EXPRESSION__OP = eINSTANCE.getAndOrExpression_Op();

    /**
     * The meta object literal for the '<em><b>Right</b></em>' containment reference feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference AND_OR_EXPRESSION__RIGHT = eINSTANCE.getAndOrExpression_Right();

    /**
     * The meta object literal for the '{@link org.deltaj.deltaj.impl.BooleanNegationImpl <em>Boolean Negation</em>}' class.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @see org.deltaj.deltaj.impl.BooleanNegationImpl
     * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getBooleanNegation()
     * @generated
     */
    EClass BOOLEAN_NEGATION = eINSTANCE.getBooleanNegation();

    /**
     * The meta object literal for the '<em><b>Expression</b></em>' containment reference feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference BOOLEAN_NEGATION__EXPRESSION = eINSTANCE.getBooleanNegation_Expression();

    /**
     * The meta object literal for the '{@link org.deltaj.deltaj.impl.ArithmeticSignedImpl <em>Arithmetic Signed</em>}' class.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @see org.deltaj.deltaj.impl.ArithmeticSignedImpl
     * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getArithmeticSigned()
     * @generated
     */
    EClass ARITHMETIC_SIGNED = eINSTANCE.getArithmeticSigned();

    /**
     * The meta object literal for the '<em><b>Expression</b></em>' containment reference feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference ARITHMETIC_SIGNED__EXPRESSION = eINSTANCE.getArithmeticSigned_Expression();

    /**
     * The meta object literal for the '{@link org.deltaj.deltaj.impl.SelectionImpl <em>Selection</em>}' class.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @see org.deltaj.deltaj.impl.SelectionImpl
     * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getSelection()
     * @generated
     */
    EClass SELECTION = eINSTANCE.getSelection();

    /**
     * The meta object literal for the '<em><b>Receiver</b></em>' containment reference feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference SELECTION__RECEIVER = eINSTANCE.getSelection_Receiver();

    /**
     * The meta object literal for the '<em><b>Message</b></em>' containment reference feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference SELECTION__MESSAGE = eINSTANCE.getSelection_Message();

    /**
     * The meta object literal for the '{@link org.deltaj.deltaj.impl.OrImpl <em>Or</em>}' class.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @see org.deltaj.deltaj.impl.OrImpl
     * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getOr()
     * @generated
     */
    EClass OR = eINSTANCE.getOr();

    /**
     * The meta object literal for the '<em><b>Left</b></em>' containment reference feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference OR__LEFT = eINSTANCE.getOr_Left();

    /**
     * The meta object literal for the '<em><b>Right</b></em>' containment reference feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference OR__RIGHT = eINSTANCE.getOr_Right();

    /**
     * The meta object literal for the '{@link org.deltaj.deltaj.impl.AndImpl <em>And</em>}' class.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @see org.deltaj.deltaj.impl.AndImpl
     * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getAnd()
     * @generated
     */
    EClass AND = eINSTANCE.getAnd();

    /**
     * The meta object literal for the '<em><b>Left</b></em>' containment reference feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference AND__LEFT = eINSTANCE.getAnd_Left();

    /**
     * The meta object literal for the '<em><b>Right</b></em>' containment reference feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference AND__RIGHT = eINSTANCE.getAnd_Right();

    /**
     * The meta object literal for the '{@link org.deltaj.deltaj.impl.FeatureRefImpl <em>Feature Ref</em>}' class.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @see org.deltaj.deltaj.impl.FeatureRefImpl
     * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getFeatureRef()
     * @generated
     */
    EClass FEATURE_REF = eINSTANCE.getFeatureRef();

    /**
     * The meta object literal for the '<em><b>Feature</b></em>' reference feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference FEATURE_REF__FEATURE = eINSTANCE.getFeatureRef_Feature();

    /**
     * The meta object literal for the '{@link org.deltaj.deltaj.impl.PropParenImpl <em>Prop Paren</em>}' class.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @see org.deltaj.deltaj.impl.PropParenImpl
     * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getPropParen()
     * @generated
     */
    EClass PROP_PAREN = eINSTANCE.getPropParen();

    /**
     * The meta object literal for the '<em><b>Formula</b></em>' containment reference feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference PROP_PAREN__FORMULA = eINSTANCE.getPropParen_Formula();

    /**
     * The meta object literal for the '{@link org.deltaj.deltaj.impl.NegationImpl <em>Negation</em>}' class.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @see org.deltaj.deltaj.impl.NegationImpl
     * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getNegation()
     * @generated
     */
    EClass NEGATION = eINSTANCE.getNegation();

    /**
     * The meta object literal for the '<em><b>Formula</b></em>' containment reference feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference NEGATION__FORMULA = eINSTANCE.getNegation_Formula();

    /**
     * The meta object literal for the '{@link org.deltaj.deltaj.impl.PropTrueImpl <em>Prop True</em>}' class.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @see org.deltaj.deltaj.impl.PropTrueImpl
     * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getPropTrue()
     * @generated
     */
    EClass PROP_TRUE = eINSTANCE.getPropTrue();

    /**
     * The meta object literal for the '{@link org.deltaj.deltaj.impl.PropFalseImpl <em>Prop False</em>}' class.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @see org.deltaj.deltaj.impl.PropFalseImpl
     * @see org.deltaj.deltaj.impl.DeltajPackageImpl#getPropFalse()
     * @generated
     */
    EClass PROP_FALSE = eINSTANCE.getPropFalse();

  }

} //DeltajPackage
