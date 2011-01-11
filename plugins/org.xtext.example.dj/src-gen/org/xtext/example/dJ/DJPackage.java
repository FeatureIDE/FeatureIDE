/**
 * <copyright>
 * </copyright>
 *
 */
package org.xtext.example.dJ;

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
 * @see org.xtext.example.dJ.DJFactory
 * @model kind="package"
 * @generated
 */
public interface DJPackage extends EPackage
{
  /**
   * The package name.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  String eNAME = "dJ";

  /**
   * The package namespace URI.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  String eNS_URI = "http://www.xtext.org/example/DJ";

  /**
   * The package namespace name.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  String eNS_PREFIX = "dJ";

  /**
   * The singleton instance of the package.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  DJPackage eINSTANCE = org.xtext.example.dJ.impl.DJPackageImpl.init();

  /**
   * The meta object id for the '{@link org.xtext.example.dJ.impl.ProgramImpl <em>Program</em>}' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see org.xtext.example.dJ.impl.ProgramImpl
   * @see org.xtext.example.dJ.impl.DJPackageImpl#getProgram()
   * @generated
   */
  int PROGRAM = 0;

  /**
   * The feature id for the '<em><b>Imports</b></em>' containment reference list.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int PROGRAM__IMPORTS = 0;

  /**
   * The feature id for the '<em><b>Features</b></em>' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int PROGRAM__FEATURES = 1;

  /**
   * The feature id for the '<em><b>Modules List</b></em>' containment reference list.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int PROGRAM__MODULES_LIST = 2;

  /**
   * The number of structural features of the '<em>Program</em>' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int PROGRAM_FEATURE_COUNT = 3;

  /**
   * The meta object id for the '{@link org.xtext.example.dJ.impl.ImportImpl <em>Import</em>}' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see org.xtext.example.dJ.impl.ImportImpl
   * @see org.xtext.example.dJ.impl.DJPackageImpl#getImport()
   * @generated
   */
  int IMPORT = 1;

  /**
   * The feature id for the '<em><b>Import URI</b></em>' attribute.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int IMPORT__IMPORT_URI = 0;

  /**
   * The number of structural features of the '<em>Import</em>' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int IMPORT_FEATURE_COUNT = 1;

  /**
   * The meta object id for the '{@link org.xtext.example.dJ.impl.FeaturesImpl <em>Features</em>}' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see org.xtext.example.dJ.impl.FeaturesImpl
   * @see org.xtext.example.dJ.impl.DJPackageImpl#getFeatures()
   * @generated
   */
  int FEATURES = 2;

  /**
   * The feature id for the '<em><b>Features List</b></em>' containment reference list.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int FEATURES__FEATURES_LIST = 0;

  /**
   * The feature id for the '<em><b>Configuration</b></em>' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int FEATURES__CONFIGURATION = 1;

  /**
   * The number of structural features of the '<em>Features</em>' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int FEATURES_FEATURE_COUNT = 2;

  /**
   * The meta object id for the '{@link org.xtext.example.dJ.impl.FeatureImpl <em>Feature</em>}' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see org.xtext.example.dJ.impl.FeatureImpl
   * @see org.xtext.example.dJ.impl.DJPackageImpl#getFeature()
   * @generated
   */
  int FEATURE = 3;

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
   * The meta object id for the '{@link org.xtext.example.dJ.impl.ModuleImpl <em>Module</em>}' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see org.xtext.example.dJ.impl.ModuleImpl
   * @see org.xtext.example.dJ.impl.DJPackageImpl#getModule()
   * @generated
   */
  int MODULE = 4;

  /**
   * The feature id for the '<em><b>Ntype</b></em>' attribute.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int MODULE__NTYPE = 0;

  /**
   * The feature id for the '<em><b>Core</b></em>' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int MODULE__CORE = 1;

  /**
   * The feature id for the '<em><b>Delta</b></em>' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int MODULE__DELTA = 2;

  /**
   * The number of structural features of the '<em>Module</em>' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int MODULE_FEATURE_COUNT = 3;

  /**
   * The meta object id for the '{@link org.xtext.example.dJ.impl.CoreImpl <em>Core</em>}' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see org.xtext.example.dJ.impl.CoreImpl
   * @see org.xtext.example.dJ.impl.DJPackageImpl#getCore()
   * @generated
   */
  int CORE = 5;

  /**
   * The feature id for the '<em><b>Name</b></em>' reference list.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int CORE__NAME = 0;

  /**
   * The feature id for the '<em><b>Classes List</b></em>' containment reference list.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int CORE__CLASSES_LIST = 1;

  /**
   * The number of structural features of the '<em>Core</em>' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int CORE_FEATURE_COUNT = 2;

  /**
   * The meta object id for the '{@link org.xtext.example.dJ.impl.ClassImpl <em>Class</em>}' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see org.xtext.example.dJ.impl.ClassImpl
   * @see org.xtext.example.dJ.impl.DJPackageImpl#getClass_()
   * @generated
   */
  int CLASS = 6;

  /**
   * The feature id for the '<em><b>Name</b></em>' attribute.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int CLASS__NAME = 0;

  /**
   * The feature id for the '<em><b>Extends</b></em>' reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int CLASS__EXTENDS = 1;

  /**
   * The feature id for the '<em><b>Field</b></em>' containment reference list.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int CLASS__FIELD = 2;

  /**
   * The feature id for the '<em><b>Constructor</b></em>' containment reference list.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int CLASS__CONSTRUCTOR = 3;

  /**
   * The feature id for the '<em><b>Method</b></em>' containment reference list.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int CLASS__METHOD = 4;

  /**
   * The number of structural features of the '<em>Class</em>' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int CLASS_FEATURE_COUNT = 5;

  /**
   * The meta object id for the '{@link org.xtext.example.dJ.impl.ConstructorImpl <em>Constructor</em>}' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see org.xtext.example.dJ.impl.ConstructorImpl
   * @see org.xtext.example.dJ.impl.DJPackageImpl#getConstructor()
   * @generated
   */
  int CONSTRUCTOR = 7;

  /**
   * The feature id for the '<em><b>Name</b></em>' reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int CONSTRUCTOR__NAME = 0;

  /**
   * The feature id for the '<em><b>Params</b></em>' containment reference list.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int CONSTRUCTOR__PARAMS = 1;

  /**
   * The feature id for the '<em><b>Constructor Super Expression</b></em>' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int CONSTRUCTOR__CONSTRUCTOR_SUPER_EXPRESSION = 2;

  /**
   * The feature id for the '<em><b>Constructor Field Expression</b></em>' containment reference list.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int CONSTRUCTOR__CONSTRUCTOR_FIELD_EXPRESSION = 3;

  /**
   * The number of structural features of the '<em>Constructor</em>' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int CONSTRUCTOR_FEATURE_COUNT = 4;

  /**
   * The meta object id for the '{@link org.xtext.example.dJ.impl.ConstructorSuperExpressionImpl <em>Constructor Super Expression</em>}' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see org.xtext.example.dJ.impl.ConstructorSuperExpressionImpl
   * @see org.xtext.example.dJ.impl.DJPackageImpl#getConstructorSuperExpression()
   * @generated
   */
  int CONSTRUCTOR_SUPER_EXPRESSION = 8;

  /**
   * The feature id for the '<em><b>Par S</b></em>' reference list.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int CONSTRUCTOR_SUPER_EXPRESSION__PAR_S = 0;

  /**
   * The number of structural features of the '<em>Constructor Super Expression</em>' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int CONSTRUCTOR_SUPER_EXPRESSION_FEATURE_COUNT = 1;

  /**
   * The meta object id for the '{@link org.xtext.example.dJ.impl.ConstructorFieldExpressionImpl <em>Constructor Field Expression</em>}' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see org.xtext.example.dJ.impl.ConstructorFieldExpressionImpl
   * @see org.xtext.example.dJ.impl.DJPackageImpl#getConstructorFieldExpression()
   * @generated
   */
  int CONSTRUCTOR_FIELD_EXPRESSION = 9;

  /**
   * The feature id for the '<em><b>Field</b></em>' reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int CONSTRUCTOR_FIELD_EXPRESSION__FIELD = 0;

  /**
   * The feature id for the '<em><b>Par T</b></em>' reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int CONSTRUCTOR_FIELD_EXPRESSION__PAR_T = 1;

  /**
   * The number of structural features of the '<em>Constructor Field Expression</em>' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int CONSTRUCTOR_FIELD_EXPRESSION_FEATURE_COUNT = 2;

  /**
   * The meta object id for the '{@link org.xtext.example.dJ.impl.FieldImpl <em>Field</em>}' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see org.xtext.example.dJ.impl.FieldImpl
   * @see org.xtext.example.dJ.impl.DJPackageImpl#getField()
   * @generated
   */
  int FIELD = 10;

  /**
   * The feature id for the '<em><b>Type</b></em>' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int FIELD__TYPE = 0;

  /**
   * The feature id for the '<em><b>Reference</b></em>' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int FIELD__REFERENCE = 1;

  /**
   * The number of structural features of the '<em>Field</em>' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int FIELD_FEATURE_COUNT = 2;

  /**
   * The meta object id for the '{@link org.xtext.example.dJ.impl.FieldRefImpl <em>Field Ref</em>}' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see org.xtext.example.dJ.impl.FieldRefImpl
   * @see org.xtext.example.dJ.impl.DJPackageImpl#getFieldRef()
   * @generated
   */
  int FIELD_REF = 11;

  /**
   * The feature id for the '<em><b>Name</b></em>' attribute.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int FIELD_REF__NAME = 0;

  /**
   * The number of structural features of the '<em>Field Ref</em>' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int FIELD_REF_FEATURE_COUNT = 1;

  /**
   * The meta object id for the '{@link org.xtext.example.dJ.impl.ParameterImpl <em>Parameter</em>}' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see org.xtext.example.dJ.impl.ParameterImpl
   * @see org.xtext.example.dJ.impl.DJPackageImpl#getParameter()
   * @generated
   */
  int PARAMETER = 12;

  /**
   * The feature id for the '<em><b>Type</b></em>' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int PARAMETER__TYPE = 0;

  /**
   * The feature id for the '<em><b>Name</b></em>' attribute.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int PARAMETER__NAME = 1;

  /**
   * The number of structural features of the '<em>Parameter</em>' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int PARAMETER_FEATURE_COUNT = 2;

  /**
   * The meta object id for the '{@link org.xtext.example.dJ.impl.MethodImpl <em>Method</em>}' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see org.xtext.example.dJ.impl.MethodImpl
   * @see org.xtext.example.dJ.impl.DJPackageImpl#getMethod()
   * @generated
   */
  int METHOD = 13;

  /**
   * The feature id for the '<em><b>Returntype</b></em>' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int METHOD__RETURNTYPE = 0;

  /**
   * The feature id for the '<em><b>Reference</b></em>' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int METHOD__REFERENCE = 1;

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
   * The meta object id for the '{@link org.xtext.example.dJ.impl.MethodRefImpl <em>Method Ref</em>}' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see org.xtext.example.dJ.impl.MethodRefImpl
   * @see org.xtext.example.dJ.impl.DJPackageImpl#getMethodRef()
   * @generated
   */
  int METHOD_REF = 14;

  /**
   * The feature id for the '<em><b>Name</b></em>' attribute.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int METHOD_REF__NAME = 0;

  /**
   * The number of structural features of the '<em>Method Ref</em>' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int METHOD_REF_FEATURE_COUNT = 1;

  /**
   * The meta object id for the '{@link org.xtext.example.dJ.impl.MethodBodyImpl <em>Method Body</em>}' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see org.xtext.example.dJ.impl.MethodBodyImpl
   * @see org.xtext.example.dJ.impl.DJPackageImpl#getMethodBody()
   * @generated
   */
  int METHOD_BODY = 15;

  /**
   * The feature id for the '<em><b>Insert Java</b></em>' containment reference list.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int METHOD_BODY__INSERT_JAVA = 0;

  /**
   * The feature id for the '<em><b>Expressions</b></em>' containment reference list.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int METHOD_BODY__EXPRESSIONS = 1;

  /**
   * The feature id for the '<em><b>Return</b></em>' attribute.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int METHOD_BODY__RETURN = 2;

  /**
   * The feature id for the '<em><b>Expression Return</b></em>' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int METHOD_BODY__EXPRESSION_RETURN = 3;

  /**
   * The number of structural features of the '<em>Method Body</em>' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int METHOD_BODY_FEATURE_COUNT = 4;

  /**
   * The meta object id for the '{@link org.xtext.example.dJ.impl.DeltaImpl <em>Delta</em>}' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see org.xtext.example.dJ.impl.DeltaImpl
   * @see org.xtext.example.dJ.impl.DJPackageImpl#getDelta()
   * @generated
   */
  int DELTA = 16;

  /**
   * The feature id for the '<em><b>Name</b></em>' attribute.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int DELTA__NAME = 0;

  /**
   * The feature id for the '<em><b>After</b></em>' reference list.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int DELTA__AFTER = 1;

  /**
   * The feature id for the '<em><b>Condition</b></em>' containment reference list.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int DELTA__CONDITION = 2;

  /**
   * The feature id for the '<em><b>Classes List</b></em>' containment reference list.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int DELTA__CLASSES_LIST = 3;

  /**
   * The number of structural features of the '<em>Delta</em>' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int DELTA_FEATURE_COUNT = 4;

  /**
   * The meta object id for the '{@link org.xtext.example.dJ.impl.ConfigurationImpl <em>Configuration</em>}' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see org.xtext.example.dJ.impl.ConfigurationImpl
   * @see org.xtext.example.dJ.impl.DJPackageImpl#getConfiguration()
   * @generated
   */
  int CONFIGURATION = 17;

  /**
   * The feature id for the '<em><b>Feature List</b></em>' containment reference list.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int CONFIGURATION__FEATURE_LIST = 0;

  /**
   * The number of structural features of the '<em>Configuration</em>' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int CONFIGURATION_FEATURE_COUNT = 1;

  /**
   * The meta object id for the '{@link org.xtext.example.dJ.impl.ConfigImpl <em>Config</em>}' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see org.xtext.example.dJ.impl.ConfigImpl
   * @see org.xtext.example.dJ.impl.DJPackageImpl#getConfig()
   * @generated
   */
  int CONFIG = 18;

  /**
   * The feature id for the '<em><b>Feature</b></em>' reference list.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int CONFIG__FEATURE = 0;

  /**
   * The number of structural features of the '<em>Config</em>' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int CONFIG_FEATURE_COUNT = 1;

  /**
   * The meta object id for the '{@link org.xtext.example.dJ.impl.ConditionImpl <em>Condition</em>}' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see org.xtext.example.dJ.impl.ConditionImpl
   * @see org.xtext.example.dJ.impl.DJPackageImpl#getCondition()
   * @generated
   */
  int CONDITION = 19;

  /**
   * The feature id for the '<em><b>Complement</b></em>' attribute.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int CONDITION__COMPLEMENT = 0;

  /**
   * The feature id for the '<em><b>Condition1</b></em>' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int CONDITION__CONDITION1 = 1;

  /**
   * The feature id for the '<em><b>Operation</b></em>' attribute.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int CONDITION__OPERATION = 2;

  /**
   * The feature id for the '<em><b>Condition2</b></em>' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int CONDITION__CONDITION2 = 3;

  /**
   * The feature id for the '<em><b>Feature</b></em>' reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int CONDITION__FEATURE = 4;

  /**
   * The number of structural features of the '<em>Condition</em>' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int CONDITION_FEATURE_COUNT = 5;

  /**
   * The meta object id for the '{@link org.xtext.example.dJ.impl.ClassmImpl <em>Classm</em>}' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see org.xtext.example.dJ.impl.ClassmImpl
   * @see org.xtext.example.dJ.impl.DJPackageImpl#getClassm()
   * @generated
   */
  int CLASSM = 20;

  /**
   * The feature id for the '<em><b>Action</b></em>' attribute.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int CLASSM__ACTION = 0;

  /**
   * The feature id for the '<em><b>Modifies</b></em>' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int CLASSM__MODIFIES = 1;

  /**
   * The feature id for the '<em><b>Adds</b></em>' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int CLASSM__ADDS = 2;

  /**
   * The feature id for the '<em><b>Remove</b></em>' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int CLASSM__REMOVE = 3;

  /**
   * The number of structural features of the '<em>Classm</em>' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int CLASSM_FEATURE_COUNT = 4;

  /**
   * The meta object id for the '{@link org.xtext.example.dJ.impl.ModifiesClassImpl <em>Modifies Class</em>}' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see org.xtext.example.dJ.impl.ModifiesClassImpl
   * @see org.xtext.example.dJ.impl.DJPackageImpl#getModifiesClass()
   * @generated
   */
  int MODIFIES_CLASS = 21;

  /**
   * The feature id for the '<em><b>Class</b></em>' reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int MODIFIES_CLASS__CLASS = 0;

  /**
   * The feature id for the '<em><b>Extends</b></em>' reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int MODIFIES_CLASS__EXTENDS = 1;

  /**
   * The feature id for the '<em><b>Field</b></em>' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int MODIFIES_CLASS__FIELD = 2;

  /**
   * The feature id for the '<em><b>Constructor</b></em>' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int MODIFIES_CLASS__CONSTRUCTOR = 3;

  /**
   * The feature id for the '<em><b>Method</b></em>' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int MODIFIES_CLASS__METHOD = 4;

  /**
   * The number of structural features of the '<em>Modifies Class</em>' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int MODIFIES_CLASS_FEATURE_COUNT = 5;

  /**
   * The meta object id for the '{@link org.xtext.example.dJ.impl.AddsClassImpl <em>Adds Class</em>}' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see org.xtext.example.dJ.impl.AddsClassImpl
   * @see org.xtext.example.dJ.impl.DJPackageImpl#getAddsClass()
   * @generated
   */
  int ADDS_CLASS = 22;

  /**
   * The feature id for the '<em><b>Class</b></em>' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int ADDS_CLASS__CLASS = 0;

  /**
   * The number of structural features of the '<em>Adds Class</em>' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int ADDS_CLASS_FEATURE_COUNT = 1;

  /**
   * The meta object id for the '{@link org.xtext.example.dJ.impl.RemoveClassImpl <em>Remove Class</em>}' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see org.xtext.example.dJ.impl.RemoveClassImpl
   * @see org.xtext.example.dJ.impl.DJPackageImpl#getRemoveClass()
   * @generated
   */
  int REMOVE_CLASS = 23;

  /**
   * The feature id for the '<em><b>Class</b></em>' reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int REMOVE_CLASS__CLASS = 0;

  /**
   * The number of structural features of the '<em>Remove Class</em>' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int REMOVE_CLASS_FEATURE_COUNT = 1;

  /**
   * The meta object id for the '{@link org.xtext.example.dJ.impl.MethodmImpl <em>Methodm</em>}' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see org.xtext.example.dJ.impl.MethodmImpl
   * @see org.xtext.example.dJ.impl.DJPackageImpl#getMethodm()
   * @generated
   */
  int METHODM = 24;

  /**
   * The feature id for the '<em><b>Remove List</b></em>' containment reference list.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int METHODM__REMOVE_LIST = 0;

  /**
   * The feature id for the '<em><b>Modifies List</b></em>' containment reference list.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int METHODM__MODIFIES_LIST = 1;

  /**
   * The feature id for the '<em><b>Adds List</b></em>' containment reference list.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int METHODM__ADDS_LIST = 2;

  /**
   * The number of structural features of the '<em>Methodm</em>' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int METHODM_FEATURE_COUNT = 3;

  /**
   * The meta object id for the '{@link org.xtext.example.dJ.impl.AddsMethodImpl <em>Adds Method</em>}' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see org.xtext.example.dJ.impl.AddsMethodImpl
   * @see org.xtext.example.dJ.impl.DJPackageImpl#getAddsMethod()
   * @generated
   */
  int ADDS_METHOD = 25;

  /**
   * The feature id for the '<em><b>Method</b></em>' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int ADDS_METHOD__METHOD = 0;

  /**
   * The number of structural features of the '<em>Adds Method</em>' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int ADDS_METHOD_FEATURE_COUNT = 1;

  /**
   * The meta object id for the '{@link org.xtext.example.dJ.impl.ModifiesMethodImpl <em>Modifies Method</em>}' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see org.xtext.example.dJ.impl.ModifiesMethodImpl
   * @see org.xtext.example.dJ.impl.DJPackageImpl#getModifiesMethod()
   * @generated
   */
  int MODIFIES_METHOD = 26;

  /**
   * The feature id for the '<em><b>Returntype</b></em>' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int MODIFIES_METHOD__RETURNTYPE = 0;

  /**
   * The feature id for the '<em><b>Method Ref</b></em>' reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int MODIFIES_METHOD__METHOD_REF = 1;

  /**
   * The feature id for the '<em><b>Params</b></em>' containment reference list.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int MODIFIES_METHOD__PARAMS = 2;

  /**
   * The feature id for the '<em><b>Body</b></em>' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int MODIFIES_METHOD__BODY = 3;

  /**
   * The number of structural features of the '<em>Modifies Method</em>' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int MODIFIES_METHOD_FEATURE_COUNT = 4;

  /**
   * The meta object id for the '{@link org.xtext.example.dJ.impl.RemovesMethodImpl <em>Removes Method</em>}' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see org.xtext.example.dJ.impl.RemovesMethodImpl
   * @see org.xtext.example.dJ.impl.DJPackageImpl#getRemovesMethod()
   * @generated
   */
  int REMOVES_METHOD = 27;

  /**
   * The feature id for the '<em><b>Method Ref</b></em>' reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int REMOVES_METHOD__METHOD_REF = 0;

  /**
   * The number of structural features of the '<em>Removes Method</em>' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int REMOVES_METHOD_FEATURE_COUNT = 1;

  /**
   * The meta object id for the '{@link org.xtext.example.dJ.impl.FieldmImpl <em>Fieldm</em>}' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see org.xtext.example.dJ.impl.FieldmImpl
   * @see org.xtext.example.dJ.impl.DJPackageImpl#getFieldm()
   * @generated
   */
  int FIELDM = 28;

  /**
   * The feature id for the '<em><b>Remove List</b></em>' containment reference list.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int FIELDM__REMOVE_LIST = 0;

  /**
   * The feature id for the '<em><b>Adds List</b></em>' containment reference list.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int FIELDM__ADDS_LIST = 1;

  /**
   * The number of structural features of the '<em>Fieldm</em>' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int FIELDM_FEATURE_COUNT = 2;

  /**
   * The meta object id for the '{@link org.xtext.example.dJ.impl.AddsFieldImpl <em>Adds Field</em>}' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see org.xtext.example.dJ.impl.AddsFieldImpl
   * @see org.xtext.example.dJ.impl.DJPackageImpl#getAddsField()
   * @generated
   */
  int ADDS_FIELD = 29;

  /**
   * The feature id for the '<em><b>Field</b></em>' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int ADDS_FIELD__FIELD = 0;

  /**
   * The number of structural features of the '<em>Adds Field</em>' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int ADDS_FIELD_FEATURE_COUNT = 1;

  /**
   * The meta object id for the '{@link org.xtext.example.dJ.impl.RenamesFieldImpl <em>Renames Field</em>}' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see org.xtext.example.dJ.impl.RenamesFieldImpl
   * @see org.xtext.example.dJ.impl.DJPackageImpl#getRenamesField()
   * @generated
   */
  int RENAMES_FIELD = 30;

  /**
   * The feature id for the '<em><b>Field Ref</b></em>' reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int RENAMES_FIELD__FIELD_REF = 0;

  /**
   * The feature id for the '<em><b>New Field Ref</b></em>' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int RENAMES_FIELD__NEW_FIELD_REF = 1;

  /**
   * The number of structural features of the '<em>Renames Field</em>' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int RENAMES_FIELD_FEATURE_COUNT = 2;

  /**
   * The meta object id for the '{@link org.xtext.example.dJ.impl.RemovesFieldImpl <em>Removes Field</em>}' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see org.xtext.example.dJ.impl.RemovesFieldImpl
   * @see org.xtext.example.dJ.impl.DJPackageImpl#getRemovesField()
   * @generated
   */
  int REMOVES_FIELD = 31;

  /**
   * The feature id for the '<em><b>Field Ref</b></em>' reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int REMOVES_FIELD__FIELD_REF = 0;

  /**
   * The number of structural features of the '<em>Removes Field</em>' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int REMOVES_FIELD_FEATURE_COUNT = 1;

  /**
   * The meta object id for the '{@link org.xtext.example.dJ.impl.TypeImpl <em>Type</em>}' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see org.xtext.example.dJ.impl.TypeImpl
   * @see org.xtext.example.dJ.impl.DJPackageImpl#getType()
   * @generated
   */
  int TYPE = 32;

  /**
   * The feature id for the '<em><b>Basic</b></em>' attribute.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int TYPE__BASIC = 0;

  /**
   * The feature id for the '<em><b>Classref</b></em>' reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int TYPE__CLASSREF = 1;

  /**
   * The number of structural features of the '<em>Type</em>' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int TYPE_FEATURE_COUNT = 2;

  /**
   * The meta object id for the '{@link org.xtext.example.dJ.impl.ExpressionImpl <em>Expression</em>}' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see org.xtext.example.dJ.impl.ExpressionImpl
   * @see org.xtext.example.dJ.impl.DJPackageImpl#getExpression()
   * @generated
   */
  int EXPRESSION = 33;

  /**
   * The feature id for the '<em><b>Terminal Expression</b></em>' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int EXPRESSION__TERMINAL_EXPRESSION = 0;

  /**
   * The feature id for the '<em><b>Receiver</b></em>' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int EXPRESSION__RECEIVER = 1;

  /**
   * The feature id for the '<em><b>Message</b></em>' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int EXPRESSION__MESSAGE = 2;

  /**
   * The feature id for the '<em><b>Value</b></em>' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int EXPRESSION__VALUE = 3;

  /**
   * The number of structural features of the '<em>Expression</em>' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int EXPRESSION_FEATURE_COUNT = 4;

  /**
   * The meta object id for the '{@link org.xtext.example.dJ.impl.MessageImpl <em>Message</em>}' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see org.xtext.example.dJ.impl.MessageImpl
   * @see org.xtext.example.dJ.impl.DJPackageImpl#getMessage()
   * @generated
   */
  int MESSAGE = 34;

  /**
   * The feature id for the '<em><b>Method Call</b></em>' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int MESSAGE__METHOD_CALL = 0;

  /**
   * The feature id for the '<em><b>Field Access</b></em>' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int MESSAGE__FIELD_ACCESS = 1;

  /**
   * The number of structural features of the '<em>Message</em>' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int MESSAGE_FEATURE_COUNT = 2;

  /**
   * The meta object id for the '{@link org.xtext.example.dJ.impl.MethodCallImpl <em>Method Call</em>}' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see org.xtext.example.dJ.impl.MethodCallImpl
   * @see org.xtext.example.dJ.impl.DJPackageImpl#getMethodCall()
   * @generated
   */
  int METHOD_CALL = 35;

  /**
   * The feature id for the '<em><b>Name</b></em>' reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int METHOD_CALL__NAME = 0;

  /**
   * The feature id for the '<em><b>Args</b></em>' containment reference list.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int METHOD_CALL__ARGS = 1;

  /**
   * The number of structural features of the '<em>Method Call</em>' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int METHOD_CALL_FEATURE_COUNT = 2;

  /**
   * The meta object id for the '{@link org.xtext.example.dJ.impl.FieldAccessImpl <em>Field Access</em>}' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see org.xtext.example.dJ.impl.FieldAccessImpl
   * @see org.xtext.example.dJ.impl.DJPackageImpl#getFieldAccess()
   * @generated
   */
  int FIELD_ACCESS = 36;

  /**
   * The feature id for the '<em><b>Name</b></em>' reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int FIELD_ACCESS__NAME = 0;

  /**
   * The number of structural features of the '<em>Field Access</em>' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int FIELD_ACCESS_FEATURE_COUNT = 1;

  /**
   * The meta object id for the '{@link org.xtext.example.dJ.impl.TerminalExpressionImpl <em>Terminal Expression</em>}' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see org.xtext.example.dJ.impl.TerminalExpressionImpl
   * @see org.xtext.example.dJ.impl.DJPackageImpl#getTerminalExpression()
   * @generated
   */
  int TERMINAL_EXPRESSION = 37;

  /**
   * The feature id for the '<em><b>This</b></em>' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int TERMINAL_EXPRESSION__THIS = 0;

  /**
   * The feature id for the '<em><b>Variable</b></em>' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int TERMINAL_EXPRESSION__VARIABLE = 1;

  /**
   * The feature id for the '<em><b>New</b></em>' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int TERMINAL_EXPRESSION__NEW = 2;

  /**
   * The feature id for the '<em><b>Cast</b></em>' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int TERMINAL_EXPRESSION__CAST = 3;

  /**
   * The feature id for the '<em><b>Original</b></em>' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int TERMINAL_EXPRESSION__ORIGINAL = 4;

  /**
   * The feature id for the '<em><b>Int</b></em>' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int TERMINAL_EXPRESSION__INT = 5;

  /**
   * The feature id for the '<em><b>String</b></em>' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int TERMINAL_EXPRESSION__STRING = 6;

  /**
   * The feature id for the '<em><b>Null</b></em>' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int TERMINAL_EXPRESSION__NULL = 7;

  /**
   * The number of structural features of the '<em>Terminal Expression</em>' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int TERMINAL_EXPRESSION_FEATURE_COUNT = 8;

  /**
   * The meta object id for the '{@link org.xtext.example.dJ.impl.InsertJavaImpl <em>Insert Java</em>}' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see org.xtext.example.dJ.impl.InsertJavaImpl
   * @see org.xtext.example.dJ.impl.DJPackageImpl#getInsertJava()
   * @generated
   */
  int INSERT_JAVA = 38;

  /**
   * The feature id for the '<em><b>String</b></em>' attribute.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int INSERT_JAVA__STRING = 0;

  /**
   * The number of structural features of the '<em>Insert Java</em>' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int INSERT_JAVA_FEATURE_COUNT = 1;

  /**
   * The meta object id for the '{@link org.xtext.example.dJ.impl.ThisImpl <em>This</em>}' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see org.xtext.example.dJ.impl.ThisImpl
   * @see org.xtext.example.dJ.impl.DJPackageImpl#getThis()
   * @generated
   */
  int THIS = 39;

  /**
   * The feature id for the '<em><b>Variable</b></em>' attribute.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int THIS__VARIABLE = 0;

  /**
   * The number of structural features of the '<em>This</em>' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int THIS_FEATURE_COUNT = 1;

  /**
   * The meta object id for the '{@link org.xtext.example.dJ.impl.VariableImpl <em>Variable</em>}' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see org.xtext.example.dJ.impl.VariableImpl
   * @see org.xtext.example.dJ.impl.DJPackageImpl#getVariable()
   * @generated
   */
  int VARIABLE = 40;

  /**
   * The feature id for the '<em><b>Parameter</b></em>' reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int VARIABLE__PARAMETER = 0;

  /**
   * The feature id for the '<em><b>Field Ref</b></em>' reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int VARIABLE__FIELD_REF = 1;

  /**
   * The number of structural features of the '<em>Variable</em>' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int VARIABLE_FEATURE_COUNT = 2;

  /**
   * The meta object id for the '{@link org.xtext.example.dJ.impl.NewImpl <em>New</em>}' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see org.xtext.example.dJ.impl.NewImpl
   * @see org.xtext.example.dJ.impl.DJPackageImpl#getNew()
   * @generated
   */
  int NEW = 41;

  /**
   * The feature id for the '<em><b>Type</b></em>' reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int NEW__TYPE = 0;

  /**
   * The feature id for the '<em><b>Args</b></em>' containment reference list.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int NEW__ARGS = 1;

  /**
   * The number of structural features of the '<em>New</em>' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int NEW_FEATURE_COUNT = 2;

  /**
   * The meta object id for the '{@link org.xtext.example.dJ.impl.CastImpl <em>Cast</em>}' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see org.xtext.example.dJ.impl.CastImpl
   * @see org.xtext.example.dJ.impl.DJPackageImpl#getCast()
   * @generated
   */
  int CAST = 42;

  /**
   * The feature id for the '<em><b>Type</b></em>' reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int CAST__TYPE = 0;

  /**
   * The feature id for the '<em><b>Expression</b></em>' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int CAST__EXPRESSION = 1;

  /**
   * The number of structural features of the '<em>Cast</em>' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int CAST_FEATURE_COUNT = 2;

  /**
   * The meta object id for the '{@link org.xtext.example.dJ.impl.OriginalImpl <em>Original</em>}' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see org.xtext.example.dJ.impl.OriginalImpl
   * @see org.xtext.example.dJ.impl.DJPackageImpl#getOriginal()
   * @generated
   */
  int ORIGINAL = 43;

  /**
   * The feature id for the '<em><b>Par</b></em>' reference list.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int ORIGINAL__PAR = 0;

  /**
   * The number of structural features of the '<em>Original</em>' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int ORIGINAL_FEATURE_COUNT = 1;

  /**
   * The meta object id for the '{@link org.xtext.example.dJ.impl.InteroImpl <em>Intero</em>}' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see org.xtext.example.dJ.impl.InteroImpl
   * @see org.xtext.example.dJ.impl.DJPackageImpl#getIntero()
   * @generated
   */
  int INTERO = 44;

  /**
   * The feature id for the '<em><b>Value</b></em>' attribute.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int INTERO__VALUE = 0;

  /**
   * The number of structural features of the '<em>Intero</em>' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int INTERO_FEATURE_COUNT = 1;

  /**
   * The meta object id for the '{@link org.xtext.example.dJ.impl.StringaImpl <em>Stringa</em>}' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see org.xtext.example.dJ.impl.StringaImpl
   * @see org.xtext.example.dJ.impl.DJPackageImpl#getStringa()
   * @generated
   */
  int STRINGA = 45;

  /**
   * The feature id for the '<em><b>Value</b></em>' attribute.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int STRINGA__VALUE = 0;

  /**
   * The number of structural features of the '<em>Stringa</em>' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int STRINGA_FEATURE_COUNT = 1;

  /**
   * The meta object id for the '{@link org.xtext.example.dJ.impl.NulloImpl <em>Nullo</em>}' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see org.xtext.example.dJ.impl.NulloImpl
   * @see org.xtext.example.dJ.impl.DJPackageImpl#getNullo()
   * @generated
   */
  int NULLO = 46;

  /**
   * The feature id for the '<em><b>Value</b></em>' attribute.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int NULLO__VALUE = 0;

  /**
   * The number of structural features of the '<em>Nullo</em>' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int NULLO_FEATURE_COUNT = 1;

  /**
   * The meta object id for the '{@link org.xtext.example.dJ.impl.ArgumentImpl <em>Argument</em>}' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see org.xtext.example.dJ.impl.ArgumentImpl
   * @see org.xtext.example.dJ.impl.DJPackageImpl#getArgument()
   * @generated
   */
  int ARGUMENT = 47;

  /**
   * The feature id for the '<em><b>Expression</b></em>' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int ARGUMENT__EXPRESSION = 0;

  /**
   * The number of structural features of the '<em>Argument</em>' class.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   * @ordered
   */
  int ARGUMENT_FEATURE_COUNT = 1;


  /**
   * Returns the meta object for class '{@link org.xtext.example.dJ.Program <em>Program</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for class '<em>Program</em>'.
   * @see org.xtext.example.dJ.Program
   * @generated
   */
  EClass getProgram();

  /**
   * Returns the meta object for the containment reference list '{@link org.xtext.example.dJ.Program#getImports <em>Imports</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the containment reference list '<em>Imports</em>'.
   * @see org.xtext.example.dJ.Program#getImports()
   * @see #getProgram()
   * @generated
   */
  EReference getProgram_Imports();

  /**
   * Returns the meta object for the containment reference '{@link org.xtext.example.dJ.Program#getFeatures <em>Features</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the containment reference '<em>Features</em>'.
   * @see org.xtext.example.dJ.Program#getFeatures()
   * @see #getProgram()
   * @generated
   */
  EReference getProgram_Features();

  /**
   * Returns the meta object for the containment reference list '{@link org.xtext.example.dJ.Program#getModulesList <em>Modules List</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the containment reference list '<em>Modules List</em>'.
   * @see org.xtext.example.dJ.Program#getModulesList()
   * @see #getProgram()
   * @generated
   */
  EReference getProgram_ModulesList();

  /**
   * Returns the meta object for class '{@link org.xtext.example.dJ.Import <em>Import</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for class '<em>Import</em>'.
   * @see org.xtext.example.dJ.Import
   * @generated
   */
  EClass getImport();

  /**
   * Returns the meta object for the attribute '{@link org.xtext.example.dJ.Import#getImportURI <em>Import URI</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the attribute '<em>Import URI</em>'.
   * @see org.xtext.example.dJ.Import#getImportURI()
   * @see #getImport()
   * @generated
   */
  EAttribute getImport_ImportURI();

  /**
   * Returns the meta object for class '{@link org.xtext.example.dJ.Features <em>Features</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for class '<em>Features</em>'.
   * @see org.xtext.example.dJ.Features
   * @generated
   */
  EClass getFeatures();

  /**
   * Returns the meta object for the containment reference list '{@link org.xtext.example.dJ.Features#getFeaturesList <em>Features List</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the containment reference list '<em>Features List</em>'.
   * @see org.xtext.example.dJ.Features#getFeaturesList()
   * @see #getFeatures()
   * @generated
   */
  EReference getFeatures_FeaturesList();

  /**
   * Returns the meta object for the containment reference '{@link org.xtext.example.dJ.Features#getConfiguration <em>Configuration</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the containment reference '<em>Configuration</em>'.
   * @see org.xtext.example.dJ.Features#getConfiguration()
   * @see #getFeatures()
   * @generated
   */
  EReference getFeatures_Configuration();

  /**
   * Returns the meta object for class '{@link org.xtext.example.dJ.Feature <em>Feature</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for class '<em>Feature</em>'.
   * @see org.xtext.example.dJ.Feature
   * @generated
   */
  EClass getFeature();

  /**
   * Returns the meta object for the attribute '{@link org.xtext.example.dJ.Feature#getName <em>Name</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the attribute '<em>Name</em>'.
   * @see org.xtext.example.dJ.Feature#getName()
   * @see #getFeature()
   * @generated
   */
  EAttribute getFeature_Name();

  /**
   * Returns the meta object for class '{@link org.xtext.example.dJ.Module <em>Module</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for class '<em>Module</em>'.
   * @see org.xtext.example.dJ.Module
   * @generated
   */
  EClass getModule();

  /**
   * Returns the meta object for the attribute '{@link org.xtext.example.dJ.Module#getNtype <em>Ntype</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the attribute '<em>Ntype</em>'.
   * @see org.xtext.example.dJ.Module#getNtype()
   * @see #getModule()
   * @generated
   */
  EAttribute getModule_Ntype();

  /**
   * Returns the meta object for the containment reference '{@link org.xtext.example.dJ.Module#getCore <em>Core</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the containment reference '<em>Core</em>'.
   * @see org.xtext.example.dJ.Module#getCore()
   * @see #getModule()
   * @generated
   */
  EReference getModule_Core();

  /**
   * Returns the meta object for the containment reference '{@link org.xtext.example.dJ.Module#getDelta <em>Delta</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the containment reference '<em>Delta</em>'.
   * @see org.xtext.example.dJ.Module#getDelta()
   * @see #getModule()
   * @generated
   */
  EReference getModule_Delta();

  /**
   * Returns the meta object for class '{@link org.xtext.example.dJ.Core <em>Core</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for class '<em>Core</em>'.
   * @see org.xtext.example.dJ.Core
   * @generated
   */
  EClass getCore();

  /**
   * Returns the meta object for the reference list '{@link org.xtext.example.dJ.Core#getName <em>Name</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the reference list '<em>Name</em>'.
   * @see org.xtext.example.dJ.Core#getName()
   * @see #getCore()
   * @generated
   */
  EReference getCore_Name();

  /**
   * Returns the meta object for the containment reference list '{@link org.xtext.example.dJ.Core#getClassesList <em>Classes List</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the containment reference list '<em>Classes List</em>'.
   * @see org.xtext.example.dJ.Core#getClassesList()
   * @see #getCore()
   * @generated
   */
  EReference getCore_ClassesList();

  /**
   * Returns the meta object for class '{@link org.xtext.example.dJ.Class <em>Class</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for class '<em>Class</em>'.
   * @see org.xtext.example.dJ.Class
   * @generated
   */
  EClass getClass_();

  /**
   * Returns the meta object for the attribute '{@link org.xtext.example.dJ.Class#getName <em>Name</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the attribute '<em>Name</em>'.
   * @see org.xtext.example.dJ.Class#getName()
   * @see #getClass_()
   * @generated
   */
  EAttribute getClass_Name();

  /**
   * Returns the meta object for the reference '{@link org.xtext.example.dJ.Class#getExtends <em>Extends</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the reference '<em>Extends</em>'.
   * @see org.xtext.example.dJ.Class#getExtends()
   * @see #getClass_()
   * @generated
   */
  EReference getClass_Extends();

  /**
   * Returns the meta object for the containment reference list '{@link org.xtext.example.dJ.Class#getField <em>Field</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the containment reference list '<em>Field</em>'.
   * @see org.xtext.example.dJ.Class#getField()
   * @see #getClass_()
   * @generated
   */
  EReference getClass_Field();

  /**
   * Returns the meta object for the containment reference list '{@link org.xtext.example.dJ.Class#getConstructor <em>Constructor</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the containment reference list '<em>Constructor</em>'.
   * @see org.xtext.example.dJ.Class#getConstructor()
   * @see #getClass_()
   * @generated
   */
  EReference getClass_Constructor();

  /**
   * Returns the meta object for the containment reference list '{@link org.xtext.example.dJ.Class#getMethod <em>Method</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the containment reference list '<em>Method</em>'.
   * @see org.xtext.example.dJ.Class#getMethod()
   * @see #getClass_()
   * @generated
   */
  EReference getClass_Method();

  /**
   * Returns the meta object for class '{@link org.xtext.example.dJ.Constructor <em>Constructor</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for class '<em>Constructor</em>'.
   * @see org.xtext.example.dJ.Constructor
   * @generated
   */
  EClass getConstructor();

  /**
   * Returns the meta object for the reference '{@link org.xtext.example.dJ.Constructor#getName <em>Name</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the reference '<em>Name</em>'.
   * @see org.xtext.example.dJ.Constructor#getName()
   * @see #getConstructor()
   * @generated
   */
  EReference getConstructor_Name();

  /**
   * Returns the meta object for the containment reference list '{@link org.xtext.example.dJ.Constructor#getParams <em>Params</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the containment reference list '<em>Params</em>'.
   * @see org.xtext.example.dJ.Constructor#getParams()
   * @see #getConstructor()
   * @generated
   */
  EReference getConstructor_Params();

  /**
   * Returns the meta object for the containment reference '{@link org.xtext.example.dJ.Constructor#getConstructorSuperExpression <em>Constructor Super Expression</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the containment reference '<em>Constructor Super Expression</em>'.
   * @see org.xtext.example.dJ.Constructor#getConstructorSuperExpression()
   * @see #getConstructor()
   * @generated
   */
  EReference getConstructor_ConstructorSuperExpression();

  /**
   * Returns the meta object for the containment reference list '{@link org.xtext.example.dJ.Constructor#getConstructorFieldExpression <em>Constructor Field Expression</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the containment reference list '<em>Constructor Field Expression</em>'.
   * @see org.xtext.example.dJ.Constructor#getConstructorFieldExpression()
   * @see #getConstructor()
   * @generated
   */
  EReference getConstructor_ConstructorFieldExpression();

  /**
   * Returns the meta object for class '{@link org.xtext.example.dJ.ConstructorSuperExpression <em>Constructor Super Expression</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for class '<em>Constructor Super Expression</em>'.
   * @see org.xtext.example.dJ.ConstructorSuperExpression
   * @generated
   */
  EClass getConstructorSuperExpression();

  /**
   * Returns the meta object for the reference list '{@link org.xtext.example.dJ.ConstructorSuperExpression#getParS <em>Par S</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the reference list '<em>Par S</em>'.
   * @see org.xtext.example.dJ.ConstructorSuperExpression#getParS()
   * @see #getConstructorSuperExpression()
   * @generated
   */
  EReference getConstructorSuperExpression_ParS();

  /**
   * Returns the meta object for class '{@link org.xtext.example.dJ.ConstructorFieldExpression <em>Constructor Field Expression</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for class '<em>Constructor Field Expression</em>'.
   * @see org.xtext.example.dJ.ConstructorFieldExpression
   * @generated
   */
  EClass getConstructorFieldExpression();

  /**
   * Returns the meta object for the reference '{@link org.xtext.example.dJ.ConstructorFieldExpression#getField <em>Field</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the reference '<em>Field</em>'.
   * @see org.xtext.example.dJ.ConstructorFieldExpression#getField()
   * @see #getConstructorFieldExpression()
   * @generated
   */
  EReference getConstructorFieldExpression_Field();

  /**
   * Returns the meta object for the reference '{@link org.xtext.example.dJ.ConstructorFieldExpression#getParT <em>Par T</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the reference '<em>Par T</em>'.
   * @see org.xtext.example.dJ.ConstructorFieldExpression#getParT()
   * @see #getConstructorFieldExpression()
   * @generated
   */
  EReference getConstructorFieldExpression_ParT();

  /**
   * Returns the meta object for class '{@link org.xtext.example.dJ.Field <em>Field</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for class '<em>Field</em>'.
   * @see org.xtext.example.dJ.Field
   * @generated
   */
  EClass getField();

  /**
   * Returns the meta object for the containment reference '{@link org.xtext.example.dJ.Field#getType <em>Type</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the containment reference '<em>Type</em>'.
   * @see org.xtext.example.dJ.Field#getType()
   * @see #getField()
   * @generated
   */
  EReference getField_Type();

  /**
   * Returns the meta object for the containment reference '{@link org.xtext.example.dJ.Field#getReference <em>Reference</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the containment reference '<em>Reference</em>'.
   * @see org.xtext.example.dJ.Field#getReference()
   * @see #getField()
   * @generated
   */
  EReference getField_Reference();

  /**
   * Returns the meta object for class '{@link org.xtext.example.dJ.FieldRef <em>Field Ref</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for class '<em>Field Ref</em>'.
   * @see org.xtext.example.dJ.FieldRef
   * @generated
   */
  EClass getFieldRef();

  /**
   * Returns the meta object for the attribute '{@link org.xtext.example.dJ.FieldRef#getName <em>Name</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the attribute '<em>Name</em>'.
   * @see org.xtext.example.dJ.FieldRef#getName()
   * @see #getFieldRef()
   * @generated
   */
  EAttribute getFieldRef_Name();

  /**
   * Returns the meta object for class '{@link org.xtext.example.dJ.Parameter <em>Parameter</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for class '<em>Parameter</em>'.
   * @see org.xtext.example.dJ.Parameter
   * @generated
   */
  EClass getParameter();

  /**
   * Returns the meta object for the containment reference '{@link org.xtext.example.dJ.Parameter#getType <em>Type</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the containment reference '<em>Type</em>'.
   * @see org.xtext.example.dJ.Parameter#getType()
   * @see #getParameter()
   * @generated
   */
  EReference getParameter_Type();

  /**
   * Returns the meta object for the attribute '{@link org.xtext.example.dJ.Parameter#getName <em>Name</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the attribute '<em>Name</em>'.
   * @see org.xtext.example.dJ.Parameter#getName()
   * @see #getParameter()
   * @generated
   */
  EAttribute getParameter_Name();

  /**
   * Returns the meta object for class '{@link org.xtext.example.dJ.Method <em>Method</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for class '<em>Method</em>'.
   * @see org.xtext.example.dJ.Method
   * @generated
   */
  EClass getMethod();

  /**
   * Returns the meta object for the containment reference '{@link org.xtext.example.dJ.Method#getReturntype <em>Returntype</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the containment reference '<em>Returntype</em>'.
   * @see org.xtext.example.dJ.Method#getReturntype()
   * @see #getMethod()
   * @generated
   */
  EReference getMethod_Returntype();

  /**
   * Returns the meta object for the containment reference '{@link org.xtext.example.dJ.Method#getReference <em>Reference</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the containment reference '<em>Reference</em>'.
   * @see org.xtext.example.dJ.Method#getReference()
   * @see #getMethod()
   * @generated
   */
  EReference getMethod_Reference();

  /**
   * Returns the meta object for the containment reference list '{@link org.xtext.example.dJ.Method#getParams <em>Params</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the containment reference list '<em>Params</em>'.
   * @see org.xtext.example.dJ.Method#getParams()
   * @see #getMethod()
   * @generated
   */
  EReference getMethod_Params();

  /**
   * Returns the meta object for the containment reference '{@link org.xtext.example.dJ.Method#getBody <em>Body</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the containment reference '<em>Body</em>'.
   * @see org.xtext.example.dJ.Method#getBody()
   * @see #getMethod()
   * @generated
   */
  EReference getMethod_Body();

  /**
   * Returns the meta object for class '{@link org.xtext.example.dJ.MethodRef <em>Method Ref</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for class '<em>Method Ref</em>'.
   * @see org.xtext.example.dJ.MethodRef
   * @generated
   */
  EClass getMethodRef();

  /**
   * Returns the meta object for the attribute '{@link org.xtext.example.dJ.MethodRef#getName <em>Name</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the attribute '<em>Name</em>'.
   * @see org.xtext.example.dJ.MethodRef#getName()
   * @see #getMethodRef()
   * @generated
   */
  EAttribute getMethodRef_Name();

  /**
   * Returns the meta object for class '{@link org.xtext.example.dJ.MethodBody <em>Method Body</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for class '<em>Method Body</em>'.
   * @see org.xtext.example.dJ.MethodBody
   * @generated
   */
  EClass getMethodBody();

  /**
   * Returns the meta object for the containment reference list '{@link org.xtext.example.dJ.MethodBody#getInsertJava <em>Insert Java</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the containment reference list '<em>Insert Java</em>'.
   * @see org.xtext.example.dJ.MethodBody#getInsertJava()
   * @see #getMethodBody()
   * @generated
   */
  EReference getMethodBody_InsertJava();

  /**
   * Returns the meta object for the containment reference list '{@link org.xtext.example.dJ.MethodBody#getExpressions <em>Expressions</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the containment reference list '<em>Expressions</em>'.
   * @see org.xtext.example.dJ.MethodBody#getExpressions()
   * @see #getMethodBody()
   * @generated
   */
  EReference getMethodBody_Expressions();

  /**
   * Returns the meta object for the attribute '{@link org.xtext.example.dJ.MethodBody#getReturn <em>Return</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the attribute '<em>Return</em>'.
   * @see org.xtext.example.dJ.MethodBody#getReturn()
   * @see #getMethodBody()
   * @generated
   */
  EAttribute getMethodBody_Return();

  /**
   * Returns the meta object for the containment reference '{@link org.xtext.example.dJ.MethodBody#getExpressionReturn <em>Expression Return</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the containment reference '<em>Expression Return</em>'.
   * @see org.xtext.example.dJ.MethodBody#getExpressionReturn()
   * @see #getMethodBody()
   * @generated
   */
  EReference getMethodBody_ExpressionReturn();

  /**
   * Returns the meta object for class '{@link org.xtext.example.dJ.Delta <em>Delta</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for class '<em>Delta</em>'.
   * @see org.xtext.example.dJ.Delta
   * @generated
   */
  EClass getDelta();

  /**
   * Returns the meta object for the attribute '{@link org.xtext.example.dJ.Delta#getName <em>Name</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the attribute '<em>Name</em>'.
   * @see org.xtext.example.dJ.Delta#getName()
   * @see #getDelta()
   * @generated
   */
  EAttribute getDelta_Name();

  /**
   * Returns the meta object for the reference list '{@link org.xtext.example.dJ.Delta#getAfter <em>After</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the reference list '<em>After</em>'.
   * @see org.xtext.example.dJ.Delta#getAfter()
   * @see #getDelta()
   * @generated
   */
  EReference getDelta_After();

  /**
   * Returns the meta object for the containment reference list '{@link org.xtext.example.dJ.Delta#getCondition <em>Condition</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the containment reference list '<em>Condition</em>'.
   * @see org.xtext.example.dJ.Delta#getCondition()
   * @see #getDelta()
   * @generated
   */
  EReference getDelta_Condition();

  /**
   * Returns the meta object for the containment reference list '{@link org.xtext.example.dJ.Delta#getClassesList <em>Classes List</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the containment reference list '<em>Classes List</em>'.
   * @see org.xtext.example.dJ.Delta#getClassesList()
   * @see #getDelta()
   * @generated
   */
  EReference getDelta_ClassesList();

  /**
   * Returns the meta object for class '{@link org.xtext.example.dJ.Configuration <em>Configuration</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for class '<em>Configuration</em>'.
   * @see org.xtext.example.dJ.Configuration
   * @generated
   */
  EClass getConfiguration();

  /**
   * Returns the meta object for the containment reference list '{@link org.xtext.example.dJ.Configuration#getFeatureList <em>Feature List</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the containment reference list '<em>Feature List</em>'.
   * @see org.xtext.example.dJ.Configuration#getFeatureList()
   * @see #getConfiguration()
   * @generated
   */
  EReference getConfiguration_FeatureList();

  /**
   * Returns the meta object for class '{@link org.xtext.example.dJ.Config <em>Config</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for class '<em>Config</em>'.
   * @see org.xtext.example.dJ.Config
   * @generated
   */
  EClass getConfig();

  /**
   * Returns the meta object for the reference list '{@link org.xtext.example.dJ.Config#getFeature <em>Feature</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the reference list '<em>Feature</em>'.
   * @see org.xtext.example.dJ.Config#getFeature()
   * @see #getConfig()
   * @generated
   */
  EReference getConfig_Feature();

  /**
   * Returns the meta object for class '{@link org.xtext.example.dJ.Condition <em>Condition</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for class '<em>Condition</em>'.
   * @see org.xtext.example.dJ.Condition
   * @generated
   */
  EClass getCondition();

  /**
   * Returns the meta object for the attribute '{@link org.xtext.example.dJ.Condition#getComplement <em>Complement</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the attribute '<em>Complement</em>'.
   * @see org.xtext.example.dJ.Condition#getComplement()
   * @see #getCondition()
   * @generated
   */
  EAttribute getCondition_Complement();

  /**
   * Returns the meta object for the containment reference '{@link org.xtext.example.dJ.Condition#getCondition1 <em>Condition1</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the containment reference '<em>Condition1</em>'.
   * @see org.xtext.example.dJ.Condition#getCondition1()
   * @see #getCondition()
   * @generated
   */
  EReference getCondition_Condition1();

  /**
   * Returns the meta object for the attribute '{@link org.xtext.example.dJ.Condition#getOperation <em>Operation</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the attribute '<em>Operation</em>'.
   * @see org.xtext.example.dJ.Condition#getOperation()
   * @see #getCondition()
   * @generated
   */
  EAttribute getCondition_Operation();

  /**
   * Returns the meta object for the containment reference '{@link org.xtext.example.dJ.Condition#getCondition2 <em>Condition2</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the containment reference '<em>Condition2</em>'.
   * @see org.xtext.example.dJ.Condition#getCondition2()
   * @see #getCondition()
   * @generated
   */
  EReference getCondition_Condition2();

  /**
   * Returns the meta object for the reference '{@link org.xtext.example.dJ.Condition#getFeature <em>Feature</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the reference '<em>Feature</em>'.
   * @see org.xtext.example.dJ.Condition#getFeature()
   * @see #getCondition()
   * @generated
   */
  EReference getCondition_Feature();

  /**
   * Returns the meta object for class '{@link org.xtext.example.dJ.Classm <em>Classm</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for class '<em>Classm</em>'.
   * @see org.xtext.example.dJ.Classm
   * @generated
   */
  EClass getClassm();

  /**
   * Returns the meta object for the attribute '{@link org.xtext.example.dJ.Classm#getAction <em>Action</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the attribute '<em>Action</em>'.
   * @see org.xtext.example.dJ.Classm#getAction()
   * @see #getClassm()
   * @generated
   */
  EAttribute getClassm_Action();

  /**
   * Returns the meta object for the containment reference '{@link org.xtext.example.dJ.Classm#getModifies <em>Modifies</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the containment reference '<em>Modifies</em>'.
   * @see org.xtext.example.dJ.Classm#getModifies()
   * @see #getClassm()
   * @generated
   */
  EReference getClassm_Modifies();

  /**
   * Returns the meta object for the containment reference '{@link org.xtext.example.dJ.Classm#getAdds <em>Adds</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the containment reference '<em>Adds</em>'.
   * @see org.xtext.example.dJ.Classm#getAdds()
   * @see #getClassm()
   * @generated
   */
  EReference getClassm_Adds();

  /**
   * Returns the meta object for the containment reference '{@link org.xtext.example.dJ.Classm#getRemove <em>Remove</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the containment reference '<em>Remove</em>'.
   * @see org.xtext.example.dJ.Classm#getRemove()
   * @see #getClassm()
   * @generated
   */
  EReference getClassm_Remove();

  /**
   * Returns the meta object for class '{@link org.xtext.example.dJ.ModifiesClass <em>Modifies Class</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for class '<em>Modifies Class</em>'.
   * @see org.xtext.example.dJ.ModifiesClass
   * @generated
   */
  EClass getModifiesClass();

  /**
   * Returns the meta object for the reference '{@link org.xtext.example.dJ.ModifiesClass#getClass_ <em>Class</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the reference '<em>Class</em>'.
   * @see org.xtext.example.dJ.ModifiesClass#getClass_()
   * @see #getModifiesClass()
   * @generated
   */
  EReference getModifiesClass_Class();

  /**
   * Returns the meta object for the reference '{@link org.xtext.example.dJ.ModifiesClass#getExtends <em>Extends</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the reference '<em>Extends</em>'.
   * @see org.xtext.example.dJ.ModifiesClass#getExtends()
   * @see #getModifiesClass()
   * @generated
   */
  EReference getModifiesClass_Extends();

  /**
   * Returns the meta object for the containment reference '{@link org.xtext.example.dJ.ModifiesClass#getField <em>Field</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the containment reference '<em>Field</em>'.
   * @see org.xtext.example.dJ.ModifiesClass#getField()
   * @see #getModifiesClass()
   * @generated
   */
  EReference getModifiesClass_Field();

  /**
   * Returns the meta object for the containment reference '{@link org.xtext.example.dJ.ModifiesClass#getConstructor <em>Constructor</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the containment reference '<em>Constructor</em>'.
   * @see org.xtext.example.dJ.ModifiesClass#getConstructor()
   * @see #getModifiesClass()
   * @generated
   */
  EReference getModifiesClass_Constructor();

  /**
   * Returns the meta object for the containment reference '{@link org.xtext.example.dJ.ModifiesClass#getMethod <em>Method</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the containment reference '<em>Method</em>'.
   * @see org.xtext.example.dJ.ModifiesClass#getMethod()
   * @see #getModifiesClass()
   * @generated
   */
  EReference getModifiesClass_Method();

  /**
   * Returns the meta object for class '{@link org.xtext.example.dJ.AddsClass <em>Adds Class</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for class '<em>Adds Class</em>'.
   * @see org.xtext.example.dJ.AddsClass
   * @generated
   */
  EClass getAddsClass();

  /**
   * Returns the meta object for the containment reference '{@link org.xtext.example.dJ.AddsClass#getClass_ <em>Class</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the containment reference '<em>Class</em>'.
   * @see org.xtext.example.dJ.AddsClass#getClass_()
   * @see #getAddsClass()
   * @generated
   */
  EReference getAddsClass_Class();

  /**
   * Returns the meta object for class '{@link org.xtext.example.dJ.RemoveClass <em>Remove Class</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for class '<em>Remove Class</em>'.
   * @see org.xtext.example.dJ.RemoveClass
   * @generated
   */
  EClass getRemoveClass();

  /**
   * Returns the meta object for the reference '{@link org.xtext.example.dJ.RemoveClass#getClass_ <em>Class</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the reference '<em>Class</em>'.
   * @see org.xtext.example.dJ.RemoveClass#getClass_()
   * @see #getRemoveClass()
   * @generated
   */
  EReference getRemoveClass_Class();

  /**
   * Returns the meta object for class '{@link org.xtext.example.dJ.Methodm <em>Methodm</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for class '<em>Methodm</em>'.
   * @see org.xtext.example.dJ.Methodm
   * @generated
   */
  EClass getMethodm();

  /**
   * Returns the meta object for the containment reference list '{@link org.xtext.example.dJ.Methodm#getRemoveList <em>Remove List</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the containment reference list '<em>Remove List</em>'.
   * @see org.xtext.example.dJ.Methodm#getRemoveList()
   * @see #getMethodm()
   * @generated
   */
  EReference getMethodm_RemoveList();

  /**
   * Returns the meta object for the containment reference list '{@link org.xtext.example.dJ.Methodm#getModifiesList <em>Modifies List</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the containment reference list '<em>Modifies List</em>'.
   * @see org.xtext.example.dJ.Methodm#getModifiesList()
   * @see #getMethodm()
   * @generated
   */
  EReference getMethodm_ModifiesList();

  /**
   * Returns the meta object for the containment reference list '{@link org.xtext.example.dJ.Methodm#getAddsList <em>Adds List</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the containment reference list '<em>Adds List</em>'.
   * @see org.xtext.example.dJ.Methodm#getAddsList()
   * @see #getMethodm()
   * @generated
   */
  EReference getMethodm_AddsList();

  /**
   * Returns the meta object for class '{@link org.xtext.example.dJ.AddsMethod <em>Adds Method</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for class '<em>Adds Method</em>'.
   * @see org.xtext.example.dJ.AddsMethod
   * @generated
   */
  EClass getAddsMethod();

  /**
   * Returns the meta object for the containment reference '{@link org.xtext.example.dJ.AddsMethod#getMethod <em>Method</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the containment reference '<em>Method</em>'.
   * @see org.xtext.example.dJ.AddsMethod#getMethod()
   * @see #getAddsMethod()
   * @generated
   */
  EReference getAddsMethod_Method();

  /**
   * Returns the meta object for class '{@link org.xtext.example.dJ.ModifiesMethod <em>Modifies Method</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for class '<em>Modifies Method</em>'.
   * @see org.xtext.example.dJ.ModifiesMethod
   * @generated
   */
  EClass getModifiesMethod();

  /**
   * Returns the meta object for the containment reference '{@link org.xtext.example.dJ.ModifiesMethod#getReturntype <em>Returntype</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the containment reference '<em>Returntype</em>'.
   * @see org.xtext.example.dJ.ModifiesMethod#getReturntype()
   * @see #getModifiesMethod()
   * @generated
   */
  EReference getModifiesMethod_Returntype();

  /**
   * Returns the meta object for the reference '{@link org.xtext.example.dJ.ModifiesMethod#getMethodRef <em>Method Ref</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the reference '<em>Method Ref</em>'.
   * @see org.xtext.example.dJ.ModifiesMethod#getMethodRef()
   * @see #getModifiesMethod()
   * @generated
   */
  EReference getModifiesMethod_MethodRef();

  /**
   * Returns the meta object for the containment reference list '{@link org.xtext.example.dJ.ModifiesMethod#getParams <em>Params</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the containment reference list '<em>Params</em>'.
   * @see org.xtext.example.dJ.ModifiesMethod#getParams()
   * @see #getModifiesMethod()
   * @generated
   */
  EReference getModifiesMethod_Params();

  /**
   * Returns the meta object for the containment reference '{@link org.xtext.example.dJ.ModifiesMethod#getBody <em>Body</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the containment reference '<em>Body</em>'.
   * @see org.xtext.example.dJ.ModifiesMethod#getBody()
   * @see #getModifiesMethod()
   * @generated
   */
  EReference getModifiesMethod_Body();

  /**
   * Returns the meta object for class '{@link org.xtext.example.dJ.RemovesMethod <em>Removes Method</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for class '<em>Removes Method</em>'.
   * @see org.xtext.example.dJ.RemovesMethod
   * @generated
   */
  EClass getRemovesMethod();

  /**
   * Returns the meta object for the reference '{@link org.xtext.example.dJ.RemovesMethod#getMethodRef <em>Method Ref</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the reference '<em>Method Ref</em>'.
   * @see org.xtext.example.dJ.RemovesMethod#getMethodRef()
   * @see #getRemovesMethod()
   * @generated
   */
  EReference getRemovesMethod_MethodRef();

  /**
   * Returns the meta object for class '{@link org.xtext.example.dJ.Fieldm <em>Fieldm</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for class '<em>Fieldm</em>'.
   * @see org.xtext.example.dJ.Fieldm
   * @generated
   */
  EClass getFieldm();

  /**
   * Returns the meta object for the containment reference list '{@link org.xtext.example.dJ.Fieldm#getRemoveList <em>Remove List</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the containment reference list '<em>Remove List</em>'.
   * @see org.xtext.example.dJ.Fieldm#getRemoveList()
   * @see #getFieldm()
   * @generated
   */
  EReference getFieldm_RemoveList();

  /**
   * Returns the meta object for the containment reference list '{@link org.xtext.example.dJ.Fieldm#getAddsList <em>Adds List</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the containment reference list '<em>Adds List</em>'.
   * @see org.xtext.example.dJ.Fieldm#getAddsList()
   * @see #getFieldm()
   * @generated
   */
  EReference getFieldm_AddsList();

  /**
   * Returns the meta object for class '{@link org.xtext.example.dJ.AddsField <em>Adds Field</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for class '<em>Adds Field</em>'.
   * @see org.xtext.example.dJ.AddsField
   * @generated
   */
  EClass getAddsField();

  /**
   * Returns the meta object for the containment reference '{@link org.xtext.example.dJ.AddsField#getField <em>Field</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the containment reference '<em>Field</em>'.
   * @see org.xtext.example.dJ.AddsField#getField()
   * @see #getAddsField()
   * @generated
   */
  EReference getAddsField_Field();

  /**
   * Returns the meta object for class '{@link org.xtext.example.dJ.RenamesField <em>Renames Field</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for class '<em>Renames Field</em>'.
   * @see org.xtext.example.dJ.RenamesField
   * @generated
   */
  EClass getRenamesField();

  /**
   * Returns the meta object for the reference '{@link org.xtext.example.dJ.RenamesField#getFieldRef <em>Field Ref</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the reference '<em>Field Ref</em>'.
   * @see org.xtext.example.dJ.RenamesField#getFieldRef()
   * @see #getRenamesField()
   * @generated
   */
  EReference getRenamesField_FieldRef();

  /**
   * Returns the meta object for the containment reference '{@link org.xtext.example.dJ.RenamesField#getNewFieldRef <em>New Field Ref</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the containment reference '<em>New Field Ref</em>'.
   * @see org.xtext.example.dJ.RenamesField#getNewFieldRef()
   * @see #getRenamesField()
   * @generated
   */
  EReference getRenamesField_NewFieldRef();

  /**
   * Returns the meta object for class '{@link org.xtext.example.dJ.RemovesField <em>Removes Field</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for class '<em>Removes Field</em>'.
   * @see org.xtext.example.dJ.RemovesField
   * @generated
   */
  EClass getRemovesField();

  /**
   * Returns the meta object for the reference '{@link org.xtext.example.dJ.RemovesField#getFieldRef <em>Field Ref</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the reference '<em>Field Ref</em>'.
   * @see org.xtext.example.dJ.RemovesField#getFieldRef()
   * @see #getRemovesField()
   * @generated
   */
  EReference getRemovesField_FieldRef();

  /**
   * Returns the meta object for class '{@link org.xtext.example.dJ.Type <em>Type</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for class '<em>Type</em>'.
   * @see org.xtext.example.dJ.Type
   * @generated
   */
  EClass getType();

  /**
   * Returns the meta object for the attribute '{@link org.xtext.example.dJ.Type#getBasic <em>Basic</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the attribute '<em>Basic</em>'.
   * @see org.xtext.example.dJ.Type#getBasic()
   * @see #getType()
   * @generated
   */
  EAttribute getType_Basic();

  /**
   * Returns the meta object for the reference '{@link org.xtext.example.dJ.Type#getClassref <em>Classref</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the reference '<em>Classref</em>'.
   * @see org.xtext.example.dJ.Type#getClassref()
   * @see #getType()
   * @generated
   */
  EReference getType_Classref();

  /**
   * Returns the meta object for class '{@link org.xtext.example.dJ.Expression <em>Expression</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for class '<em>Expression</em>'.
   * @see org.xtext.example.dJ.Expression
   * @generated
   */
  EClass getExpression();

  /**
   * Returns the meta object for the containment reference '{@link org.xtext.example.dJ.Expression#getTerminalExpression <em>Terminal Expression</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the containment reference '<em>Terminal Expression</em>'.
   * @see org.xtext.example.dJ.Expression#getTerminalExpression()
   * @see #getExpression()
   * @generated
   */
  EReference getExpression_TerminalExpression();

  /**
   * Returns the meta object for the containment reference '{@link org.xtext.example.dJ.Expression#getReceiver <em>Receiver</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the containment reference '<em>Receiver</em>'.
   * @see org.xtext.example.dJ.Expression#getReceiver()
   * @see #getExpression()
   * @generated
   */
  EReference getExpression_Receiver();

  /**
   * Returns the meta object for the containment reference '{@link org.xtext.example.dJ.Expression#getMessage <em>Message</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the containment reference '<em>Message</em>'.
   * @see org.xtext.example.dJ.Expression#getMessage()
   * @see #getExpression()
   * @generated
   */
  EReference getExpression_Message();

  /**
   * Returns the meta object for the containment reference '{@link org.xtext.example.dJ.Expression#getValue <em>Value</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the containment reference '<em>Value</em>'.
   * @see org.xtext.example.dJ.Expression#getValue()
   * @see #getExpression()
   * @generated
   */
  EReference getExpression_Value();

  /**
   * Returns the meta object for class '{@link org.xtext.example.dJ.Message <em>Message</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for class '<em>Message</em>'.
   * @see org.xtext.example.dJ.Message
   * @generated
   */
  EClass getMessage();

  /**
   * Returns the meta object for the containment reference '{@link org.xtext.example.dJ.Message#getMethodCall <em>Method Call</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the containment reference '<em>Method Call</em>'.
   * @see org.xtext.example.dJ.Message#getMethodCall()
   * @see #getMessage()
   * @generated
   */
  EReference getMessage_MethodCall();

  /**
   * Returns the meta object for the containment reference '{@link org.xtext.example.dJ.Message#getFieldAccess <em>Field Access</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the containment reference '<em>Field Access</em>'.
   * @see org.xtext.example.dJ.Message#getFieldAccess()
   * @see #getMessage()
   * @generated
   */
  EReference getMessage_FieldAccess();

  /**
   * Returns the meta object for class '{@link org.xtext.example.dJ.MethodCall <em>Method Call</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for class '<em>Method Call</em>'.
   * @see org.xtext.example.dJ.MethodCall
   * @generated
   */
  EClass getMethodCall();

  /**
   * Returns the meta object for the reference '{@link org.xtext.example.dJ.MethodCall#getName <em>Name</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the reference '<em>Name</em>'.
   * @see org.xtext.example.dJ.MethodCall#getName()
   * @see #getMethodCall()
   * @generated
   */
  EReference getMethodCall_Name();

  /**
   * Returns the meta object for the containment reference list '{@link org.xtext.example.dJ.MethodCall#getArgs <em>Args</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the containment reference list '<em>Args</em>'.
   * @see org.xtext.example.dJ.MethodCall#getArgs()
   * @see #getMethodCall()
   * @generated
   */
  EReference getMethodCall_Args();

  /**
   * Returns the meta object for class '{@link org.xtext.example.dJ.FieldAccess <em>Field Access</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for class '<em>Field Access</em>'.
   * @see org.xtext.example.dJ.FieldAccess
   * @generated
   */
  EClass getFieldAccess();

  /**
   * Returns the meta object for the reference '{@link org.xtext.example.dJ.FieldAccess#getName <em>Name</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the reference '<em>Name</em>'.
   * @see org.xtext.example.dJ.FieldAccess#getName()
   * @see #getFieldAccess()
   * @generated
   */
  EReference getFieldAccess_Name();

  /**
   * Returns the meta object for class '{@link org.xtext.example.dJ.TerminalExpression <em>Terminal Expression</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for class '<em>Terminal Expression</em>'.
   * @see org.xtext.example.dJ.TerminalExpression
   * @generated
   */
  EClass getTerminalExpression();

  /**
   * Returns the meta object for the containment reference '{@link org.xtext.example.dJ.TerminalExpression#getThis <em>This</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the containment reference '<em>This</em>'.
   * @see org.xtext.example.dJ.TerminalExpression#getThis()
   * @see #getTerminalExpression()
   * @generated
   */
  EReference getTerminalExpression_This();

  /**
   * Returns the meta object for the containment reference '{@link org.xtext.example.dJ.TerminalExpression#getVariable <em>Variable</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the containment reference '<em>Variable</em>'.
   * @see org.xtext.example.dJ.TerminalExpression#getVariable()
   * @see #getTerminalExpression()
   * @generated
   */
  EReference getTerminalExpression_Variable();

  /**
   * Returns the meta object for the containment reference '{@link org.xtext.example.dJ.TerminalExpression#getNew <em>New</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the containment reference '<em>New</em>'.
   * @see org.xtext.example.dJ.TerminalExpression#getNew()
   * @see #getTerminalExpression()
   * @generated
   */
  EReference getTerminalExpression_New();

  /**
   * Returns the meta object for the containment reference '{@link org.xtext.example.dJ.TerminalExpression#getCast <em>Cast</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the containment reference '<em>Cast</em>'.
   * @see org.xtext.example.dJ.TerminalExpression#getCast()
   * @see #getTerminalExpression()
   * @generated
   */
  EReference getTerminalExpression_Cast();

  /**
   * Returns the meta object for the containment reference '{@link org.xtext.example.dJ.TerminalExpression#getOriginal <em>Original</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the containment reference '<em>Original</em>'.
   * @see org.xtext.example.dJ.TerminalExpression#getOriginal()
   * @see #getTerminalExpression()
   * @generated
   */
  EReference getTerminalExpression_Original();

  /**
   * Returns the meta object for the containment reference '{@link org.xtext.example.dJ.TerminalExpression#getInt <em>Int</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the containment reference '<em>Int</em>'.
   * @see org.xtext.example.dJ.TerminalExpression#getInt()
   * @see #getTerminalExpression()
   * @generated
   */
  EReference getTerminalExpression_Int();

  /**
   * Returns the meta object for the containment reference '{@link org.xtext.example.dJ.TerminalExpression#getString <em>String</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the containment reference '<em>String</em>'.
   * @see org.xtext.example.dJ.TerminalExpression#getString()
   * @see #getTerminalExpression()
   * @generated
   */
  EReference getTerminalExpression_String();

  /**
   * Returns the meta object for the containment reference '{@link org.xtext.example.dJ.TerminalExpression#getNull <em>Null</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the containment reference '<em>Null</em>'.
   * @see org.xtext.example.dJ.TerminalExpression#getNull()
   * @see #getTerminalExpression()
   * @generated
   */
  EReference getTerminalExpression_Null();

  /**
   * Returns the meta object for class '{@link org.xtext.example.dJ.InsertJava <em>Insert Java</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for class '<em>Insert Java</em>'.
   * @see org.xtext.example.dJ.InsertJava
   * @generated
   */
  EClass getInsertJava();

  /**
   * Returns the meta object for the attribute '{@link org.xtext.example.dJ.InsertJava#getString <em>String</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the attribute '<em>String</em>'.
   * @see org.xtext.example.dJ.InsertJava#getString()
   * @see #getInsertJava()
   * @generated
   */
  EAttribute getInsertJava_String();

  /**
   * Returns the meta object for class '{@link org.xtext.example.dJ.This <em>This</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for class '<em>This</em>'.
   * @see org.xtext.example.dJ.This
   * @generated
   */
  EClass getThis();

  /**
   * Returns the meta object for the attribute '{@link org.xtext.example.dJ.This#getVariable <em>Variable</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the attribute '<em>Variable</em>'.
   * @see org.xtext.example.dJ.This#getVariable()
   * @see #getThis()
   * @generated
   */
  EAttribute getThis_Variable();

  /**
   * Returns the meta object for class '{@link org.xtext.example.dJ.Variable <em>Variable</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for class '<em>Variable</em>'.
   * @see org.xtext.example.dJ.Variable
   * @generated
   */
  EClass getVariable();

  /**
   * Returns the meta object for the reference '{@link org.xtext.example.dJ.Variable#getParameter <em>Parameter</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the reference '<em>Parameter</em>'.
   * @see org.xtext.example.dJ.Variable#getParameter()
   * @see #getVariable()
   * @generated
   */
  EReference getVariable_Parameter();

  /**
   * Returns the meta object for the reference '{@link org.xtext.example.dJ.Variable#getFieldRef <em>Field Ref</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the reference '<em>Field Ref</em>'.
   * @see org.xtext.example.dJ.Variable#getFieldRef()
   * @see #getVariable()
   * @generated
   */
  EReference getVariable_FieldRef();

  /**
   * Returns the meta object for class '{@link org.xtext.example.dJ.New <em>New</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for class '<em>New</em>'.
   * @see org.xtext.example.dJ.New
   * @generated
   */
  EClass getNew();

  /**
   * Returns the meta object for the reference '{@link org.xtext.example.dJ.New#getType <em>Type</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the reference '<em>Type</em>'.
   * @see org.xtext.example.dJ.New#getType()
   * @see #getNew()
   * @generated
   */
  EReference getNew_Type();

  /**
   * Returns the meta object for the containment reference list '{@link org.xtext.example.dJ.New#getArgs <em>Args</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the containment reference list '<em>Args</em>'.
   * @see org.xtext.example.dJ.New#getArgs()
   * @see #getNew()
   * @generated
   */
  EReference getNew_Args();

  /**
   * Returns the meta object for class '{@link org.xtext.example.dJ.Cast <em>Cast</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for class '<em>Cast</em>'.
   * @see org.xtext.example.dJ.Cast
   * @generated
   */
  EClass getCast();

  /**
   * Returns the meta object for the reference '{@link org.xtext.example.dJ.Cast#getType <em>Type</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the reference '<em>Type</em>'.
   * @see org.xtext.example.dJ.Cast#getType()
   * @see #getCast()
   * @generated
   */
  EReference getCast_Type();

  /**
   * Returns the meta object for the containment reference '{@link org.xtext.example.dJ.Cast#getExpression <em>Expression</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the containment reference '<em>Expression</em>'.
   * @see org.xtext.example.dJ.Cast#getExpression()
   * @see #getCast()
   * @generated
   */
  EReference getCast_Expression();

  /**
   * Returns the meta object for class '{@link org.xtext.example.dJ.Original <em>Original</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for class '<em>Original</em>'.
   * @see org.xtext.example.dJ.Original
   * @generated
   */
  EClass getOriginal();

  /**
   * Returns the meta object for the reference list '{@link org.xtext.example.dJ.Original#getPar <em>Par</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the reference list '<em>Par</em>'.
   * @see org.xtext.example.dJ.Original#getPar()
   * @see #getOriginal()
   * @generated
   */
  EReference getOriginal_Par();

  /**
   * Returns the meta object for class '{@link org.xtext.example.dJ.Intero <em>Intero</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for class '<em>Intero</em>'.
   * @see org.xtext.example.dJ.Intero
   * @generated
   */
  EClass getIntero();

  /**
   * Returns the meta object for the attribute '{@link org.xtext.example.dJ.Intero#getValue <em>Value</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the attribute '<em>Value</em>'.
   * @see org.xtext.example.dJ.Intero#getValue()
   * @see #getIntero()
   * @generated
   */
  EAttribute getIntero_Value();

  /**
   * Returns the meta object for class '{@link org.xtext.example.dJ.Stringa <em>Stringa</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for class '<em>Stringa</em>'.
   * @see org.xtext.example.dJ.Stringa
   * @generated
   */
  EClass getStringa();

  /**
   * Returns the meta object for the attribute '{@link org.xtext.example.dJ.Stringa#getValue <em>Value</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the attribute '<em>Value</em>'.
   * @see org.xtext.example.dJ.Stringa#getValue()
   * @see #getStringa()
   * @generated
   */
  EAttribute getStringa_Value();

  /**
   * Returns the meta object for class '{@link org.xtext.example.dJ.Nullo <em>Nullo</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for class '<em>Nullo</em>'.
   * @see org.xtext.example.dJ.Nullo
   * @generated
   */
  EClass getNullo();

  /**
   * Returns the meta object for the attribute '{@link org.xtext.example.dJ.Nullo#getValue <em>Value</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the attribute '<em>Value</em>'.
   * @see org.xtext.example.dJ.Nullo#getValue()
   * @see #getNullo()
   * @generated
   */
  EAttribute getNullo_Value();

  /**
   * Returns the meta object for class '{@link org.xtext.example.dJ.Argument <em>Argument</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for class '<em>Argument</em>'.
   * @see org.xtext.example.dJ.Argument
   * @generated
   */
  EClass getArgument();

  /**
   * Returns the meta object for the containment reference '{@link org.xtext.example.dJ.Argument#getExpression <em>Expression</em>}'.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the meta object for the containment reference '<em>Expression</em>'.
   * @see org.xtext.example.dJ.Argument#getExpression()
   * @see #getArgument()
   * @generated
   */
  EReference getArgument_Expression();

  /**
   * Returns the factory that creates the instances of the model.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the factory that creates the instances of the model.
   * @generated
   */
  DJFactory getDJFactory();

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
     * The meta object literal for the '{@link org.xtext.example.dJ.impl.ProgramImpl <em>Program</em>}' class.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @see org.xtext.example.dJ.impl.ProgramImpl
     * @see org.xtext.example.dJ.impl.DJPackageImpl#getProgram()
     * @generated
     */
    EClass PROGRAM = eINSTANCE.getProgram();

    /**
     * The meta object literal for the '<em><b>Imports</b></em>' containment reference list feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference PROGRAM__IMPORTS = eINSTANCE.getProgram_Imports();

    /**
     * The meta object literal for the '<em><b>Features</b></em>' containment reference feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference PROGRAM__FEATURES = eINSTANCE.getProgram_Features();

    /**
     * The meta object literal for the '<em><b>Modules List</b></em>' containment reference list feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference PROGRAM__MODULES_LIST = eINSTANCE.getProgram_ModulesList();

    /**
     * The meta object literal for the '{@link org.xtext.example.dJ.impl.ImportImpl <em>Import</em>}' class.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @see org.xtext.example.dJ.impl.ImportImpl
     * @see org.xtext.example.dJ.impl.DJPackageImpl#getImport()
     * @generated
     */
    EClass IMPORT = eINSTANCE.getImport();

    /**
     * The meta object literal for the '<em><b>Import URI</b></em>' attribute feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EAttribute IMPORT__IMPORT_URI = eINSTANCE.getImport_ImportURI();

    /**
     * The meta object literal for the '{@link org.xtext.example.dJ.impl.FeaturesImpl <em>Features</em>}' class.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @see org.xtext.example.dJ.impl.FeaturesImpl
     * @see org.xtext.example.dJ.impl.DJPackageImpl#getFeatures()
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
     * The meta object literal for the '<em><b>Configuration</b></em>' containment reference feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference FEATURES__CONFIGURATION = eINSTANCE.getFeatures_Configuration();

    /**
     * The meta object literal for the '{@link org.xtext.example.dJ.impl.FeatureImpl <em>Feature</em>}' class.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @see org.xtext.example.dJ.impl.FeatureImpl
     * @see org.xtext.example.dJ.impl.DJPackageImpl#getFeature()
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
     * The meta object literal for the '{@link org.xtext.example.dJ.impl.ModuleImpl <em>Module</em>}' class.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @see org.xtext.example.dJ.impl.ModuleImpl
     * @see org.xtext.example.dJ.impl.DJPackageImpl#getModule()
     * @generated
     */
    EClass MODULE = eINSTANCE.getModule();

    /**
     * The meta object literal for the '<em><b>Ntype</b></em>' attribute feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EAttribute MODULE__NTYPE = eINSTANCE.getModule_Ntype();

    /**
     * The meta object literal for the '<em><b>Core</b></em>' containment reference feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference MODULE__CORE = eINSTANCE.getModule_Core();

    /**
     * The meta object literal for the '<em><b>Delta</b></em>' containment reference feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference MODULE__DELTA = eINSTANCE.getModule_Delta();

    /**
     * The meta object literal for the '{@link org.xtext.example.dJ.impl.CoreImpl <em>Core</em>}' class.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @see org.xtext.example.dJ.impl.CoreImpl
     * @see org.xtext.example.dJ.impl.DJPackageImpl#getCore()
     * @generated
     */
    EClass CORE = eINSTANCE.getCore();

    /**
     * The meta object literal for the '<em><b>Name</b></em>' reference list feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference CORE__NAME = eINSTANCE.getCore_Name();

    /**
     * The meta object literal for the '<em><b>Classes List</b></em>' containment reference list feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference CORE__CLASSES_LIST = eINSTANCE.getCore_ClassesList();

    /**
     * The meta object literal for the '{@link org.xtext.example.dJ.impl.ClassImpl <em>Class</em>}' class.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @see org.xtext.example.dJ.impl.ClassImpl
     * @see org.xtext.example.dJ.impl.DJPackageImpl#getClass_()
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
     * The meta object literal for the '<em><b>Extends</b></em>' reference feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference CLASS__EXTENDS = eINSTANCE.getClass_Extends();

    /**
     * The meta object literal for the '<em><b>Field</b></em>' containment reference list feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference CLASS__FIELD = eINSTANCE.getClass_Field();

    /**
     * The meta object literal for the '<em><b>Constructor</b></em>' containment reference list feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference CLASS__CONSTRUCTOR = eINSTANCE.getClass_Constructor();

    /**
     * The meta object literal for the '<em><b>Method</b></em>' containment reference list feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference CLASS__METHOD = eINSTANCE.getClass_Method();

    /**
     * The meta object literal for the '{@link org.xtext.example.dJ.impl.ConstructorImpl <em>Constructor</em>}' class.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @see org.xtext.example.dJ.impl.ConstructorImpl
     * @see org.xtext.example.dJ.impl.DJPackageImpl#getConstructor()
     * @generated
     */
    EClass CONSTRUCTOR = eINSTANCE.getConstructor();

    /**
     * The meta object literal for the '<em><b>Name</b></em>' reference feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference CONSTRUCTOR__NAME = eINSTANCE.getConstructor_Name();

    /**
     * The meta object literal for the '<em><b>Params</b></em>' containment reference list feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference CONSTRUCTOR__PARAMS = eINSTANCE.getConstructor_Params();

    /**
     * The meta object literal for the '<em><b>Constructor Super Expression</b></em>' containment reference feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference CONSTRUCTOR__CONSTRUCTOR_SUPER_EXPRESSION = eINSTANCE.getConstructor_ConstructorSuperExpression();

    /**
     * The meta object literal for the '<em><b>Constructor Field Expression</b></em>' containment reference list feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference CONSTRUCTOR__CONSTRUCTOR_FIELD_EXPRESSION = eINSTANCE.getConstructor_ConstructorFieldExpression();

    /**
     * The meta object literal for the '{@link org.xtext.example.dJ.impl.ConstructorSuperExpressionImpl <em>Constructor Super Expression</em>}' class.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @see org.xtext.example.dJ.impl.ConstructorSuperExpressionImpl
     * @see org.xtext.example.dJ.impl.DJPackageImpl#getConstructorSuperExpression()
     * @generated
     */
    EClass CONSTRUCTOR_SUPER_EXPRESSION = eINSTANCE.getConstructorSuperExpression();

    /**
     * The meta object literal for the '<em><b>Par S</b></em>' reference list feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference CONSTRUCTOR_SUPER_EXPRESSION__PAR_S = eINSTANCE.getConstructorSuperExpression_ParS();

    /**
     * The meta object literal for the '{@link org.xtext.example.dJ.impl.ConstructorFieldExpressionImpl <em>Constructor Field Expression</em>}' class.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @see org.xtext.example.dJ.impl.ConstructorFieldExpressionImpl
     * @see org.xtext.example.dJ.impl.DJPackageImpl#getConstructorFieldExpression()
     * @generated
     */
    EClass CONSTRUCTOR_FIELD_EXPRESSION = eINSTANCE.getConstructorFieldExpression();

    /**
     * The meta object literal for the '<em><b>Field</b></em>' reference feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference CONSTRUCTOR_FIELD_EXPRESSION__FIELD = eINSTANCE.getConstructorFieldExpression_Field();

    /**
     * The meta object literal for the '<em><b>Par T</b></em>' reference feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference CONSTRUCTOR_FIELD_EXPRESSION__PAR_T = eINSTANCE.getConstructorFieldExpression_ParT();

    /**
     * The meta object literal for the '{@link org.xtext.example.dJ.impl.FieldImpl <em>Field</em>}' class.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @see org.xtext.example.dJ.impl.FieldImpl
     * @see org.xtext.example.dJ.impl.DJPackageImpl#getField()
     * @generated
     */
    EClass FIELD = eINSTANCE.getField();

    /**
     * The meta object literal for the '<em><b>Type</b></em>' containment reference feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference FIELD__TYPE = eINSTANCE.getField_Type();

    /**
     * The meta object literal for the '<em><b>Reference</b></em>' containment reference feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference FIELD__REFERENCE = eINSTANCE.getField_Reference();

    /**
     * The meta object literal for the '{@link org.xtext.example.dJ.impl.FieldRefImpl <em>Field Ref</em>}' class.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @see org.xtext.example.dJ.impl.FieldRefImpl
     * @see org.xtext.example.dJ.impl.DJPackageImpl#getFieldRef()
     * @generated
     */
    EClass FIELD_REF = eINSTANCE.getFieldRef();

    /**
     * The meta object literal for the '<em><b>Name</b></em>' attribute feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EAttribute FIELD_REF__NAME = eINSTANCE.getFieldRef_Name();

    /**
     * The meta object literal for the '{@link org.xtext.example.dJ.impl.ParameterImpl <em>Parameter</em>}' class.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @see org.xtext.example.dJ.impl.ParameterImpl
     * @see org.xtext.example.dJ.impl.DJPackageImpl#getParameter()
     * @generated
     */
    EClass PARAMETER = eINSTANCE.getParameter();

    /**
     * The meta object literal for the '<em><b>Type</b></em>' containment reference feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference PARAMETER__TYPE = eINSTANCE.getParameter_Type();

    /**
     * The meta object literal for the '<em><b>Name</b></em>' attribute feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EAttribute PARAMETER__NAME = eINSTANCE.getParameter_Name();

    /**
     * The meta object literal for the '{@link org.xtext.example.dJ.impl.MethodImpl <em>Method</em>}' class.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @see org.xtext.example.dJ.impl.MethodImpl
     * @see org.xtext.example.dJ.impl.DJPackageImpl#getMethod()
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
     * The meta object literal for the '<em><b>Reference</b></em>' containment reference feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference METHOD__REFERENCE = eINSTANCE.getMethod_Reference();

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
     * The meta object literal for the '{@link org.xtext.example.dJ.impl.MethodRefImpl <em>Method Ref</em>}' class.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @see org.xtext.example.dJ.impl.MethodRefImpl
     * @see org.xtext.example.dJ.impl.DJPackageImpl#getMethodRef()
     * @generated
     */
    EClass METHOD_REF = eINSTANCE.getMethodRef();

    /**
     * The meta object literal for the '<em><b>Name</b></em>' attribute feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EAttribute METHOD_REF__NAME = eINSTANCE.getMethodRef_Name();

    /**
     * The meta object literal for the '{@link org.xtext.example.dJ.impl.MethodBodyImpl <em>Method Body</em>}' class.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @see org.xtext.example.dJ.impl.MethodBodyImpl
     * @see org.xtext.example.dJ.impl.DJPackageImpl#getMethodBody()
     * @generated
     */
    EClass METHOD_BODY = eINSTANCE.getMethodBody();

    /**
     * The meta object literal for the '<em><b>Insert Java</b></em>' containment reference list feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference METHOD_BODY__INSERT_JAVA = eINSTANCE.getMethodBody_InsertJava();

    /**
     * The meta object literal for the '<em><b>Expressions</b></em>' containment reference list feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference METHOD_BODY__EXPRESSIONS = eINSTANCE.getMethodBody_Expressions();

    /**
     * The meta object literal for the '<em><b>Return</b></em>' attribute feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EAttribute METHOD_BODY__RETURN = eINSTANCE.getMethodBody_Return();

    /**
     * The meta object literal for the '<em><b>Expression Return</b></em>' containment reference feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference METHOD_BODY__EXPRESSION_RETURN = eINSTANCE.getMethodBody_ExpressionReturn();

    /**
     * The meta object literal for the '{@link org.xtext.example.dJ.impl.DeltaImpl <em>Delta</em>}' class.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @see org.xtext.example.dJ.impl.DeltaImpl
     * @see org.xtext.example.dJ.impl.DJPackageImpl#getDelta()
     * @generated
     */
    EClass DELTA = eINSTANCE.getDelta();

    /**
     * The meta object literal for the '<em><b>Name</b></em>' attribute feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EAttribute DELTA__NAME = eINSTANCE.getDelta_Name();

    /**
     * The meta object literal for the '<em><b>After</b></em>' reference list feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference DELTA__AFTER = eINSTANCE.getDelta_After();

    /**
     * The meta object literal for the '<em><b>Condition</b></em>' containment reference list feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference DELTA__CONDITION = eINSTANCE.getDelta_Condition();

    /**
     * The meta object literal for the '<em><b>Classes List</b></em>' containment reference list feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference DELTA__CLASSES_LIST = eINSTANCE.getDelta_ClassesList();

    /**
     * The meta object literal for the '{@link org.xtext.example.dJ.impl.ConfigurationImpl <em>Configuration</em>}' class.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @see org.xtext.example.dJ.impl.ConfigurationImpl
     * @see org.xtext.example.dJ.impl.DJPackageImpl#getConfiguration()
     * @generated
     */
    EClass CONFIGURATION = eINSTANCE.getConfiguration();

    /**
     * The meta object literal for the '<em><b>Feature List</b></em>' containment reference list feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference CONFIGURATION__FEATURE_LIST = eINSTANCE.getConfiguration_FeatureList();

    /**
     * The meta object literal for the '{@link org.xtext.example.dJ.impl.ConfigImpl <em>Config</em>}' class.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @see org.xtext.example.dJ.impl.ConfigImpl
     * @see org.xtext.example.dJ.impl.DJPackageImpl#getConfig()
     * @generated
     */
    EClass CONFIG = eINSTANCE.getConfig();

    /**
     * The meta object literal for the '<em><b>Feature</b></em>' reference list feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference CONFIG__FEATURE = eINSTANCE.getConfig_Feature();

    /**
     * The meta object literal for the '{@link org.xtext.example.dJ.impl.ConditionImpl <em>Condition</em>}' class.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @see org.xtext.example.dJ.impl.ConditionImpl
     * @see org.xtext.example.dJ.impl.DJPackageImpl#getCondition()
     * @generated
     */
    EClass CONDITION = eINSTANCE.getCondition();

    /**
     * The meta object literal for the '<em><b>Complement</b></em>' attribute feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EAttribute CONDITION__COMPLEMENT = eINSTANCE.getCondition_Complement();

    /**
     * The meta object literal for the '<em><b>Condition1</b></em>' containment reference feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference CONDITION__CONDITION1 = eINSTANCE.getCondition_Condition1();

    /**
     * The meta object literal for the '<em><b>Operation</b></em>' attribute feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EAttribute CONDITION__OPERATION = eINSTANCE.getCondition_Operation();

    /**
     * The meta object literal for the '<em><b>Condition2</b></em>' containment reference feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference CONDITION__CONDITION2 = eINSTANCE.getCondition_Condition2();

    /**
     * The meta object literal for the '<em><b>Feature</b></em>' reference feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference CONDITION__FEATURE = eINSTANCE.getCondition_Feature();

    /**
     * The meta object literal for the '{@link org.xtext.example.dJ.impl.ClassmImpl <em>Classm</em>}' class.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @see org.xtext.example.dJ.impl.ClassmImpl
     * @see org.xtext.example.dJ.impl.DJPackageImpl#getClassm()
     * @generated
     */
    EClass CLASSM = eINSTANCE.getClassm();

    /**
     * The meta object literal for the '<em><b>Action</b></em>' attribute feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EAttribute CLASSM__ACTION = eINSTANCE.getClassm_Action();

    /**
     * The meta object literal for the '<em><b>Modifies</b></em>' containment reference feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference CLASSM__MODIFIES = eINSTANCE.getClassm_Modifies();

    /**
     * The meta object literal for the '<em><b>Adds</b></em>' containment reference feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference CLASSM__ADDS = eINSTANCE.getClassm_Adds();

    /**
     * The meta object literal for the '<em><b>Remove</b></em>' containment reference feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference CLASSM__REMOVE = eINSTANCE.getClassm_Remove();

    /**
     * The meta object literal for the '{@link org.xtext.example.dJ.impl.ModifiesClassImpl <em>Modifies Class</em>}' class.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @see org.xtext.example.dJ.impl.ModifiesClassImpl
     * @see org.xtext.example.dJ.impl.DJPackageImpl#getModifiesClass()
     * @generated
     */
    EClass MODIFIES_CLASS = eINSTANCE.getModifiesClass();

    /**
     * The meta object literal for the '<em><b>Class</b></em>' reference feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference MODIFIES_CLASS__CLASS = eINSTANCE.getModifiesClass_Class();

    /**
     * The meta object literal for the '<em><b>Extends</b></em>' reference feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference MODIFIES_CLASS__EXTENDS = eINSTANCE.getModifiesClass_Extends();

    /**
     * The meta object literal for the '<em><b>Field</b></em>' containment reference feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference MODIFIES_CLASS__FIELD = eINSTANCE.getModifiesClass_Field();

    /**
     * The meta object literal for the '<em><b>Constructor</b></em>' containment reference feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference MODIFIES_CLASS__CONSTRUCTOR = eINSTANCE.getModifiesClass_Constructor();

    /**
     * The meta object literal for the '<em><b>Method</b></em>' containment reference feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference MODIFIES_CLASS__METHOD = eINSTANCE.getModifiesClass_Method();

    /**
     * The meta object literal for the '{@link org.xtext.example.dJ.impl.AddsClassImpl <em>Adds Class</em>}' class.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @see org.xtext.example.dJ.impl.AddsClassImpl
     * @see org.xtext.example.dJ.impl.DJPackageImpl#getAddsClass()
     * @generated
     */
    EClass ADDS_CLASS = eINSTANCE.getAddsClass();

    /**
     * The meta object literal for the '<em><b>Class</b></em>' containment reference feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference ADDS_CLASS__CLASS = eINSTANCE.getAddsClass_Class();

    /**
     * The meta object literal for the '{@link org.xtext.example.dJ.impl.RemoveClassImpl <em>Remove Class</em>}' class.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @see org.xtext.example.dJ.impl.RemoveClassImpl
     * @see org.xtext.example.dJ.impl.DJPackageImpl#getRemoveClass()
     * @generated
     */
    EClass REMOVE_CLASS = eINSTANCE.getRemoveClass();

    /**
     * The meta object literal for the '<em><b>Class</b></em>' reference feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference REMOVE_CLASS__CLASS = eINSTANCE.getRemoveClass_Class();

    /**
     * The meta object literal for the '{@link org.xtext.example.dJ.impl.MethodmImpl <em>Methodm</em>}' class.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @see org.xtext.example.dJ.impl.MethodmImpl
     * @see org.xtext.example.dJ.impl.DJPackageImpl#getMethodm()
     * @generated
     */
    EClass METHODM = eINSTANCE.getMethodm();

    /**
     * The meta object literal for the '<em><b>Remove List</b></em>' containment reference list feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference METHODM__REMOVE_LIST = eINSTANCE.getMethodm_RemoveList();

    /**
     * The meta object literal for the '<em><b>Modifies List</b></em>' containment reference list feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference METHODM__MODIFIES_LIST = eINSTANCE.getMethodm_ModifiesList();

    /**
     * The meta object literal for the '<em><b>Adds List</b></em>' containment reference list feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference METHODM__ADDS_LIST = eINSTANCE.getMethodm_AddsList();

    /**
     * The meta object literal for the '{@link org.xtext.example.dJ.impl.AddsMethodImpl <em>Adds Method</em>}' class.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @see org.xtext.example.dJ.impl.AddsMethodImpl
     * @see org.xtext.example.dJ.impl.DJPackageImpl#getAddsMethod()
     * @generated
     */
    EClass ADDS_METHOD = eINSTANCE.getAddsMethod();

    /**
     * The meta object literal for the '<em><b>Method</b></em>' containment reference feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference ADDS_METHOD__METHOD = eINSTANCE.getAddsMethod_Method();

    /**
     * The meta object literal for the '{@link org.xtext.example.dJ.impl.ModifiesMethodImpl <em>Modifies Method</em>}' class.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @see org.xtext.example.dJ.impl.ModifiesMethodImpl
     * @see org.xtext.example.dJ.impl.DJPackageImpl#getModifiesMethod()
     * @generated
     */
    EClass MODIFIES_METHOD = eINSTANCE.getModifiesMethod();

    /**
     * The meta object literal for the '<em><b>Returntype</b></em>' containment reference feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference MODIFIES_METHOD__RETURNTYPE = eINSTANCE.getModifiesMethod_Returntype();

    /**
     * The meta object literal for the '<em><b>Method Ref</b></em>' reference feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference MODIFIES_METHOD__METHOD_REF = eINSTANCE.getModifiesMethod_MethodRef();

    /**
     * The meta object literal for the '<em><b>Params</b></em>' containment reference list feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference MODIFIES_METHOD__PARAMS = eINSTANCE.getModifiesMethod_Params();

    /**
     * The meta object literal for the '<em><b>Body</b></em>' containment reference feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference MODIFIES_METHOD__BODY = eINSTANCE.getModifiesMethod_Body();

    /**
     * The meta object literal for the '{@link org.xtext.example.dJ.impl.RemovesMethodImpl <em>Removes Method</em>}' class.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @see org.xtext.example.dJ.impl.RemovesMethodImpl
     * @see org.xtext.example.dJ.impl.DJPackageImpl#getRemovesMethod()
     * @generated
     */
    EClass REMOVES_METHOD = eINSTANCE.getRemovesMethod();

    /**
     * The meta object literal for the '<em><b>Method Ref</b></em>' reference feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference REMOVES_METHOD__METHOD_REF = eINSTANCE.getRemovesMethod_MethodRef();

    /**
     * The meta object literal for the '{@link org.xtext.example.dJ.impl.FieldmImpl <em>Fieldm</em>}' class.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @see org.xtext.example.dJ.impl.FieldmImpl
     * @see org.xtext.example.dJ.impl.DJPackageImpl#getFieldm()
     * @generated
     */
    EClass FIELDM = eINSTANCE.getFieldm();

    /**
     * The meta object literal for the '<em><b>Remove List</b></em>' containment reference list feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference FIELDM__REMOVE_LIST = eINSTANCE.getFieldm_RemoveList();

    /**
     * The meta object literal for the '<em><b>Adds List</b></em>' containment reference list feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference FIELDM__ADDS_LIST = eINSTANCE.getFieldm_AddsList();

    /**
     * The meta object literal for the '{@link org.xtext.example.dJ.impl.AddsFieldImpl <em>Adds Field</em>}' class.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @see org.xtext.example.dJ.impl.AddsFieldImpl
     * @see org.xtext.example.dJ.impl.DJPackageImpl#getAddsField()
     * @generated
     */
    EClass ADDS_FIELD = eINSTANCE.getAddsField();

    /**
     * The meta object literal for the '<em><b>Field</b></em>' containment reference feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference ADDS_FIELD__FIELD = eINSTANCE.getAddsField_Field();

    /**
     * The meta object literal for the '{@link org.xtext.example.dJ.impl.RenamesFieldImpl <em>Renames Field</em>}' class.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @see org.xtext.example.dJ.impl.RenamesFieldImpl
     * @see org.xtext.example.dJ.impl.DJPackageImpl#getRenamesField()
     * @generated
     */
    EClass RENAMES_FIELD = eINSTANCE.getRenamesField();

    /**
     * The meta object literal for the '<em><b>Field Ref</b></em>' reference feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference RENAMES_FIELD__FIELD_REF = eINSTANCE.getRenamesField_FieldRef();

    /**
     * The meta object literal for the '<em><b>New Field Ref</b></em>' containment reference feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference RENAMES_FIELD__NEW_FIELD_REF = eINSTANCE.getRenamesField_NewFieldRef();

    /**
     * The meta object literal for the '{@link org.xtext.example.dJ.impl.RemovesFieldImpl <em>Removes Field</em>}' class.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @see org.xtext.example.dJ.impl.RemovesFieldImpl
     * @see org.xtext.example.dJ.impl.DJPackageImpl#getRemovesField()
     * @generated
     */
    EClass REMOVES_FIELD = eINSTANCE.getRemovesField();

    /**
     * The meta object literal for the '<em><b>Field Ref</b></em>' reference feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference REMOVES_FIELD__FIELD_REF = eINSTANCE.getRemovesField_FieldRef();

    /**
     * The meta object literal for the '{@link org.xtext.example.dJ.impl.TypeImpl <em>Type</em>}' class.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @see org.xtext.example.dJ.impl.TypeImpl
     * @see org.xtext.example.dJ.impl.DJPackageImpl#getType()
     * @generated
     */
    EClass TYPE = eINSTANCE.getType();

    /**
     * The meta object literal for the '<em><b>Basic</b></em>' attribute feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EAttribute TYPE__BASIC = eINSTANCE.getType_Basic();

    /**
     * The meta object literal for the '<em><b>Classref</b></em>' reference feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference TYPE__CLASSREF = eINSTANCE.getType_Classref();

    /**
     * The meta object literal for the '{@link org.xtext.example.dJ.impl.ExpressionImpl <em>Expression</em>}' class.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @see org.xtext.example.dJ.impl.ExpressionImpl
     * @see org.xtext.example.dJ.impl.DJPackageImpl#getExpression()
     * @generated
     */
    EClass EXPRESSION = eINSTANCE.getExpression();

    /**
     * The meta object literal for the '<em><b>Terminal Expression</b></em>' containment reference feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference EXPRESSION__TERMINAL_EXPRESSION = eINSTANCE.getExpression_TerminalExpression();

    /**
     * The meta object literal for the '<em><b>Receiver</b></em>' containment reference feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference EXPRESSION__RECEIVER = eINSTANCE.getExpression_Receiver();

    /**
     * The meta object literal for the '<em><b>Message</b></em>' containment reference feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference EXPRESSION__MESSAGE = eINSTANCE.getExpression_Message();

    /**
     * The meta object literal for the '<em><b>Value</b></em>' containment reference feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference EXPRESSION__VALUE = eINSTANCE.getExpression_Value();

    /**
     * The meta object literal for the '{@link org.xtext.example.dJ.impl.MessageImpl <em>Message</em>}' class.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @see org.xtext.example.dJ.impl.MessageImpl
     * @see org.xtext.example.dJ.impl.DJPackageImpl#getMessage()
     * @generated
     */
    EClass MESSAGE = eINSTANCE.getMessage();

    /**
     * The meta object literal for the '<em><b>Method Call</b></em>' containment reference feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference MESSAGE__METHOD_CALL = eINSTANCE.getMessage_MethodCall();

    /**
     * The meta object literal for the '<em><b>Field Access</b></em>' containment reference feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference MESSAGE__FIELD_ACCESS = eINSTANCE.getMessage_FieldAccess();

    /**
     * The meta object literal for the '{@link org.xtext.example.dJ.impl.MethodCallImpl <em>Method Call</em>}' class.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @see org.xtext.example.dJ.impl.MethodCallImpl
     * @see org.xtext.example.dJ.impl.DJPackageImpl#getMethodCall()
     * @generated
     */
    EClass METHOD_CALL = eINSTANCE.getMethodCall();

    /**
     * The meta object literal for the '<em><b>Name</b></em>' reference feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference METHOD_CALL__NAME = eINSTANCE.getMethodCall_Name();

    /**
     * The meta object literal for the '<em><b>Args</b></em>' containment reference list feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference METHOD_CALL__ARGS = eINSTANCE.getMethodCall_Args();

    /**
     * The meta object literal for the '{@link org.xtext.example.dJ.impl.FieldAccessImpl <em>Field Access</em>}' class.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @see org.xtext.example.dJ.impl.FieldAccessImpl
     * @see org.xtext.example.dJ.impl.DJPackageImpl#getFieldAccess()
     * @generated
     */
    EClass FIELD_ACCESS = eINSTANCE.getFieldAccess();

    /**
     * The meta object literal for the '<em><b>Name</b></em>' reference feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference FIELD_ACCESS__NAME = eINSTANCE.getFieldAccess_Name();

    /**
     * The meta object literal for the '{@link org.xtext.example.dJ.impl.TerminalExpressionImpl <em>Terminal Expression</em>}' class.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @see org.xtext.example.dJ.impl.TerminalExpressionImpl
     * @see org.xtext.example.dJ.impl.DJPackageImpl#getTerminalExpression()
     * @generated
     */
    EClass TERMINAL_EXPRESSION = eINSTANCE.getTerminalExpression();

    /**
     * The meta object literal for the '<em><b>This</b></em>' containment reference feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference TERMINAL_EXPRESSION__THIS = eINSTANCE.getTerminalExpression_This();

    /**
     * The meta object literal for the '<em><b>Variable</b></em>' containment reference feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference TERMINAL_EXPRESSION__VARIABLE = eINSTANCE.getTerminalExpression_Variable();

    /**
     * The meta object literal for the '<em><b>New</b></em>' containment reference feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference TERMINAL_EXPRESSION__NEW = eINSTANCE.getTerminalExpression_New();

    /**
     * The meta object literal for the '<em><b>Cast</b></em>' containment reference feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference TERMINAL_EXPRESSION__CAST = eINSTANCE.getTerminalExpression_Cast();

    /**
     * The meta object literal for the '<em><b>Original</b></em>' containment reference feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference TERMINAL_EXPRESSION__ORIGINAL = eINSTANCE.getTerminalExpression_Original();

    /**
     * The meta object literal for the '<em><b>Int</b></em>' containment reference feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference TERMINAL_EXPRESSION__INT = eINSTANCE.getTerminalExpression_Int();

    /**
     * The meta object literal for the '<em><b>String</b></em>' containment reference feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference TERMINAL_EXPRESSION__STRING = eINSTANCE.getTerminalExpression_String();

    /**
     * The meta object literal for the '<em><b>Null</b></em>' containment reference feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference TERMINAL_EXPRESSION__NULL = eINSTANCE.getTerminalExpression_Null();

    /**
     * The meta object literal for the '{@link org.xtext.example.dJ.impl.InsertJavaImpl <em>Insert Java</em>}' class.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @see org.xtext.example.dJ.impl.InsertJavaImpl
     * @see org.xtext.example.dJ.impl.DJPackageImpl#getInsertJava()
     * @generated
     */
    EClass INSERT_JAVA = eINSTANCE.getInsertJava();

    /**
     * The meta object literal for the '<em><b>String</b></em>' attribute feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EAttribute INSERT_JAVA__STRING = eINSTANCE.getInsertJava_String();

    /**
     * The meta object literal for the '{@link org.xtext.example.dJ.impl.ThisImpl <em>This</em>}' class.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @see org.xtext.example.dJ.impl.ThisImpl
     * @see org.xtext.example.dJ.impl.DJPackageImpl#getThis()
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
     * The meta object literal for the '{@link org.xtext.example.dJ.impl.VariableImpl <em>Variable</em>}' class.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @see org.xtext.example.dJ.impl.VariableImpl
     * @see org.xtext.example.dJ.impl.DJPackageImpl#getVariable()
     * @generated
     */
    EClass VARIABLE = eINSTANCE.getVariable();

    /**
     * The meta object literal for the '<em><b>Parameter</b></em>' reference feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference VARIABLE__PARAMETER = eINSTANCE.getVariable_Parameter();

    /**
     * The meta object literal for the '<em><b>Field Ref</b></em>' reference feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference VARIABLE__FIELD_REF = eINSTANCE.getVariable_FieldRef();

    /**
     * The meta object literal for the '{@link org.xtext.example.dJ.impl.NewImpl <em>New</em>}' class.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @see org.xtext.example.dJ.impl.NewImpl
     * @see org.xtext.example.dJ.impl.DJPackageImpl#getNew()
     * @generated
     */
    EClass NEW = eINSTANCE.getNew();

    /**
     * The meta object literal for the '<em><b>Type</b></em>' reference feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference NEW__TYPE = eINSTANCE.getNew_Type();

    /**
     * The meta object literal for the '<em><b>Args</b></em>' containment reference list feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference NEW__ARGS = eINSTANCE.getNew_Args();

    /**
     * The meta object literal for the '{@link org.xtext.example.dJ.impl.CastImpl <em>Cast</em>}' class.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @see org.xtext.example.dJ.impl.CastImpl
     * @see org.xtext.example.dJ.impl.DJPackageImpl#getCast()
     * @generated
     */
    EClass CAST = eINSTANCE.getCast();

    /**
     * The meta object literal for the '<em><b>Type</b></em>' reference feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference CAST__TYPE = eINSTANCE.getCast_Type();

    /**
     * The meta object literal for the '<em><b>Expression</b></em>' containment reference feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference CAST__EXPRESSION = eINSTANCE.getCast_Expression();

    /**
     * The meta object literal for the '{@link org.xtext.example.dJ.impl.OriginalImpl <em>Original</em>}' class.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @see org.xtext.example.dJ.impl.OriginalImpl
     * @see org.xtext.example.dJ.impl.DJPackageImpl#getOriginal()
     * @generated
     */
    EClass ORIGINAL = eINSTANCE.getOriginal();

    /**
     * The meta object literal for the '<em><b>Par</b></em>' reference list feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference ORIGINAL__PAR = eINSTANCE.getOriginal_Par();

    /**
     * The meta object literal for the '{@link org.xtext.example.dJ.impl.InteroImpl <em>Intero</em>}' class.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @see org.xtext.example.dJ.impl.InteroImpl
     * @see org.xtext.example.dJ.impl.DJPackageImpl#getIntero()
     * @generated
     */
    EClass INTERO = eINSTANCE.getIntero();

    /**
     * The meta object literal for the '<em><b>Value</b></em>' attribute feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EAttribute INTERO__VALUE = eINSTANCE.getIntero_Value();

    /**
     * The meta object literal for the '{@link org.xtext.example.dJ.impl.StringaImpl <em>Stringa</em>}' class.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @see org.xtext.example.dJ.impl.StringaImpl
     * @see org.xtext.example.dJ.impl.DJPackageImpl#getStringa()
     * @generated
     */
    EClass STRINGA = eINSTANCE.getStringa();

    /**
     * The meta object literal for the '<em><b>Value</b></em>' attribute feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EAttribute STRINGA__VALUE = eINSTANCE.getStringa_Value();

    /**
     * The meta object literal for the '{@link org.xtext.example.dJ.impl.NulloImpl <em>Nullo</em>}' class.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @see org.xtext.example.dJ.impl.NulloImpl
     * @see org.xtext.example.dJ.impl.DJPackageImpl#getNullo()
     * @generated
     */
    EClass NULLO = eINSTANCE.getNullo();

    /**
     * The meta object literal for the '<em><b>Value</b></em>' attribute feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EAttribute NULLO__VALUE = eINSTANCE.getNullo_Value();

    /**
     * The meta object literal for the '{@link org.xtext.example.dJ.impl.ArgumentImpl <em>Argument</em>}' class.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @see org.xtext.example.dJ.impl.ArgumentImpl
     * @see org.xtext.example.dJ.impl.DJPackageImpl#getArgument()
     * @generated
     */
    EClass ARGUMENT = eINSTANCE.getArgument();

    /**
     * The meta object literal for the '<em><b>Expression</b></em>' containment reference feature.
     * <!-- begin-user-doc -->
     * <!-- end-user-doc -->
     * @generated
     */
    EReference ARGUMENT__EXPRESSION = eINSTANCE.getArgument_Expression();

  }

} //DJPackage
