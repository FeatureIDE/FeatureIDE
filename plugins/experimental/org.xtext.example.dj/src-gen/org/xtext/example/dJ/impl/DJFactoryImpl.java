/**
 * <copyright>
 * </copyright>
 *
 */
package org.xtext.example.dJ.impl;

import org.eclipse.emf.ecore.EClass;
import org.eclipse.emf.ecore.EObject;
import org.eclipse.emf.ecore.EPackage;

import org.eclipse.emf.ecore.impl.EFactoryImpl;

import org.eclipse.emf.ecore.plugin.EcorePlugin;

import org.xtext.example.dJ.AddsClass;
import org.xtext.example.dJ.AddsField;
import org.xtext.example.dJ.AddsMethod;
import org.xtext.example.dJ.Argument;
import org.xtext.example.dJ.Cast;
import org.xtext.example.dJ.Classm;
import org.xtext.example.dJ.Condition;
import org.xtext.example.dJ.Config;
import org.xtext.example.dJ.Configuration;
import org.xtext.example.dJ.Constructor;
import org.xtext.example.dJ.ConstructorFieldExpression;
import org.xtext.example.dJ.ConstructorSuperExpression;
import org.xtext.example.dJ.Core;
import org.xtext.example.dJ.DJFactory;
import org.xtext.example.dJ.DJPackage;
import org.xtext.example.dJ.Delta;
import org.xtext.example.dJ.Expression;
import org.xtext.example.dJ.Feature;
import org.xtext.example.dJ.Features;
import org.xtext.example.dJ.Field;
import org.xtext.example.dJ.FieldAccess;
import org.xtext.example.dJ.FieldRef;
import org.xtext.example.dJ.Fieldm;
import org.xtext.example.dJ.Import;
import org.xtext.example.dJ.InsertJava;
import org.xtext.example.dJ.Intero;
import org.xtext.example.dJ.Message;
import org.xtext.example.dJ.Method;
import org.xtext.example.dJ.MethodBody;
import org.xtext.example.dJ.MethodCall;
import org.xtext.example.dJ.MethodRef;
import org.xtext.example.dJ.Methodm;
import org.xtext.example.dJ.ModifiesClass;
import org.xtext.example.dJ.ModifiesMethod;
import org.xtext.example.dJ.Module;
import org.xtext.example.dJ.New;
import org.xtext.example.dJ.Nullo;
import org.xtext.example.dJ.Original;
import org.xtext.example.dJ.Parameter;
import org.xtext.example.dJ.Program;
import org.xtext.example.dJ.RemoveClass;
import org.xtext.example.dJ.RemovesField;
import org.xtext.example.dJ.RemovesMethod;
import org.xtext.example.dJ.RenamesField;
import org.xtext.example.dJ.Stringa;
import org.xtext.example.dJ.TerminalExpression;
import org.xtext.example.dJ.This;
import org.xtext.example.dJ.Type;
import org.xtext.example.dJ.Variable;

/**
 * <!-- begin-user-doc -->
 * An implementation of the model <b>Factory</b>.
 * <!-- end-user-doc -->
 * @generated
 */
public class DJFactoryImpl extends EFactoryImpl implements DJFactory
{
  /**
   * Creates the default factory implementation.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public static DJFactory init()
  {
    try
    {
      DJFactory theDJFactory = (DJFactory)EPackage.Registry.INSTANCE.getEFactory("http://www.xtext.org/example/DJ"); 
      if (theDJFactory != null)
      {
        return theDJFactory;
      }
    }
    catch (Exception exception)
    {
      EcorePlugin.INSTANCE.log(exception);
    }
    return new DJFactoryImpl();
  }

  /**
   * Creates an instance of the factory.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public DJFactoryImpl()
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
      case DJPackage.PROGRAM: return createProgram();
      case DJPackage.IMPORT: return createImport();
      case DJPackage.FEATURES: return createFeatures();
      case DJPackage.FEATURE: return createFeature();
      case DJPackage.MODULE: return createModule();
      case DJPackage.CORE: return createCore();
      case DJPackage.CLASS: return createClass();
      case DJPackage.CONSTRUCTOR: return createConstructor();
      case DJPackage.CONSTRUCTOR_SUPER_EXPRESSION: return createConstructorSuperExpression();
      case DJPackage.CONSTRUCTOR_FIELD_EXPRESSION: return createConstructorFieldExpression();
      case DJPackage.FIELD: return createField();
      case DJPackage.FIELD_REF: return createFieldRef();
      case DJPackage.PARAMETER: return createParameter();
      case DJPackage.METHOD: return createMethod();
      case DJPackage.METHOD_REF: return createMethodRef();
      case DJPackage.METHOD_BODY: return createMethodBody();
      case DJPackage.DELTA: return createDelta();
      case DJPackage.CONFIGURATION: return createConfiguration();
      case DJPackage.CONFIG: return createConfig();
      case DJPackage.CONDITION: return createCondition();
      case DJPackage.CLASSM: return createClassm();
      case DJPackage.MODIFIES_CLASS: return createModifiesClass();
      case DJPackage.ADDS_CLASS: return createAddsClass();
      case DJPackage.REMOVE_CLASS: return createRemoveClass();
      case DJPackage.METHODM: return createMethodm();
      case DJPackage.ADDS_METHOD: return createAddsMethod();
      case DJPackage.MODIFIES_METHOD: return createModifiesMethod();
      case DJPackage.REMOVES_METHOD: return createRemovesMethod();
      case DJPackage.FIELDM: return createFieldm();
      case DJPackage.ADDS_FIELD: return createAddsField();
      case DJPackage.RENAMES_FIELD: return createRenamesField();
      case DJPackage.REMOVES_FIELD: return createRemovesField();
      case DJPackage.TYPE: return createType();
      case DJPackage.EXPRESSION: return createExpression();
      case DJPackage.MESSAGE: return createMessage();
      case DJPackage.METHOD_CALL: return createMethodCall();
      case DJPackage.FIELD_ACCESS: return createFieldAccess();
      case DJPackage.TERMINAL_EXPRESSION: return createTerminalExpression();
      case DJPackage.INSERT_JAVA: return createInsertJava();
      case DJPackage.THIS: return createThis();
      case DJPackage.VARIABLE: return createVariable();
      case DJPackage.NEW: return createNew();
      case DJPackage.CAST: return createCast();
      case DJPackage.ORIGINAL: return createOriginal();
      case DJPackage.INTERO: return createIntero();
      case DJPackage.STRINGA: return createStringa();
      case DJPackage.NULLO: return createNullo();
      case DJPackage.ARGUMENT: return createArgument();
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
  public Import createImport()
  {
    ImportImpl import_ = new ImportImpl();
    return import_;
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
  public Module createModule()
  {
    ModuleImpl module = new ModuleImpl();
    return module;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public Core createCore()
  {
    CoreImpl core = new CoreImpl();
    return core;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public org.xtext.example.dJ.Class createClass()
  {
    ClassImpl class_ = new ClassImpl();
    return class_;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public Constructor createConstructor()
  {
    ConstructorImpl constructor = new ConstructorImpl();
    return constructor;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public ConstructorSuperExpression createConstructorSuperExpression()
  {
    ConstructorSuperExpressionImpl constructorSuperExpression = new ConstructorSuperExpressionImpl();
    return constructorSuperExpression;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public ConstructorFieldExpression createConstructorFieldExpression()
  {
    ConstructorFieldExpressionImpl constructorFieldExpression = new ConstructorFieldExpressionImpl();
    return constructorFieldExpression;
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
  public FieldRef createFieldRef()
  {
    FieldRefImpl fieldRef = new FieldRefImpl();
    return fieldRef;
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
  public MethodRef createMethodRef()
  {
    MethodRefImpl methodRef = new MethodRefImpl();
    return methodRef;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public MethodBody createMethodBody()
  {
    MethodBodyImpl methodBody = new MethodBodyImpl();
    return methodBody;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public Delta createDelta()
  {
    DeltaImpl delta = new DeltaImpl();
    return delta;
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
  public Config createConfig()
  {
    ConfigImpl config = new ConfigImpl();
    return config;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public Condition createCondition()
  {
    ConditionImpl condition = new ConditionImpl();
    return condition;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public Classm createClassm()
  {
    ClassmImpl classm = new ClassmImpl();
    return classm;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public ModifiesClass createModifiesClass()
  {
    ModifiesClassImpl modifiesClass = new ModifiesClassImpl();
    return modifiesClass;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public AddsClass createAddsClass()
  {
    AddsClassImpl addsClass = new AddsClassImpl();
    return addsClass;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public RemoveClass createRemoveClass()
  {
    RemoveClassImpl removeClass = new RemoveClassImpl();
    return removeClass;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public Methodm createMethodm()
  {
    MethodmImpl methodm = new MethodmImpl();
    return methodm;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public AddsMethod createAddsMethod()
  {
    AddsMethodImpl addsMethod = new AddsMethodImpl();
    return addsMethod;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public ModifiesMethod createModifiesMethod()
  {
    ModifiesMethodImpl modifiesMethod = new ModifiesMethodImpl();
    return modifiesMethod;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public RemovesMethod createRemovesMethod()
  {
    RemovesMethodImpl removesMethod = new RemovesMethodImpl();
    return removesMethod;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public Fieldm createFieldm()
  {
    FieldmImpl fieldm = new FieldmImpl();
    return fieldm;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public AddsField createAddsField()
  {
    AddsFieldImpl addsField = new AddsFieldImpl();
    return addsField;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public RenamesField createRenamesField()
  {
    RenamesFieldImpl renamesField = new RenamesFieldImpl();
    return renamesField;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public RemovesField createRemovesField()
  {
    RemovesFieldImpl removesField = new RemovesFieldImpl();
    return removesField;
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
  public FieldAccess createFieldAccess()
  {
    FieldAccessImpl fieldAccess = new FieldAccessImpl();
    return fieldAccess;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public TerminalExpression createTerminalExpression()
  {
    TerminalExpressionImpl terminalExpression = new TerminalExpressionImpl();
    return terminalExpression;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public InsertJava createInsertJava()
  {
    InsertJavaImpl insertJava = new InsertJavaImpl();
    return insertJava;
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
  public Variable createVariable()
  {
    VariableImpl variable = new VariableImpl();
    return variable;
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
  public Intero createIntero()
  {
    InteroImpl intero = new InteroImpl();
    return intero;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public Stringa createStringa()
  {
    StringaImpl stringa = new StringaImpl();
    return stringa;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public Nullo createNullo()
  {
    NulloImpl nullo = new NulloImpl();
    return nullo;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public Argument createArgument()
  {
    ArgumentImpl argument = new ArgumentImpl();
    return argument;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public DJPackage getDJPackage()
  {
    return (DJPackage)getEPackage();
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @deprecated
   * @generated
   */
  @Deprecated
  public static DJPackage getPackage()
  {
    return DJPackage.eINSTANCE;
  }

} //DJFactoryImpl
