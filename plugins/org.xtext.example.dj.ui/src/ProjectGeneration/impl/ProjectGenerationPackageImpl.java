/**
 * <copyright>
 * </copyright>
 *
 * $Id$
 */
package ProjectGeneration.impl;

import ProjectGeneration.ProjectGenerationFactory;
import ProjectGeneration.ProjectGenerationPackage;
import ProjectGeneration.ProjectSettings;
import ProjectGeneration.SampleSet;

import org.eclipse.emf.ecore.EAttribute;
import org.eclipse.emf.ecore.EClass;
import org.eclipse.emf.ecore.EEnum;
import org.eclipse.emf.ecore.EPackage;

import org.eclipse.emf.ecore.impl.EPackageImpl;

/**
 * <!-- begin-user-doc -->
 * An implementation of the model <b>Package</b>.
 * <!-- end-user-doc -->
 * @generated
 */
public class ProjectGenerationPackageImpl extends EPackageImpl implements ProjectGenerationPackage {
	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private EClass projectSettingsEClass = null;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private EEnum sampleSetEEnum = null;

	/**
	 * Creates an instance of the model <b>Package</b>, registered with
	 * {@link org.eclipse.emf.ecore.EPackage.Registry EPackage.Registry} by the package
	 * package URI value.
	 * <p>Note: the correct way to create the package is via the static
	 * factory method {@link #init init()}, which also performs
	 * initialization of the package, or returns the registered package,
	 * if one already exists.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see org.eclipse.emf.ecore.EPackage.Registry
	 * @see ProjectGeneration.ProjectGenerationPackage#eNS_URI
	 * @see #init()
	 * @generated
	 */
	private ProjectGenerationPackageImpl() {
		super(eNS_URI, ProjectGenerationFactory.eINSTANCE);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private static boolean isInited = false;

	/**
	 * Creates, registers, and initializes the <b>Package</b> for this model, and for any others upon which it depends.
	 * 
	 * <p>This method is used to initialize {@link ProjectGenerationPackage#eINSTANCE} when that field is accessed.
	 * Clients should not invoke it directly. Instead, they should simply access that field to obtain the package.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #eNS_URI
	 * @see #createPackageContents()
	 * @see #initializePackageContents()
	 * @generated
	 */
	public static ProjectGenerationPackage init() {
		if (isInited) return (ProjectGenerationPackage)EPackage.Registry.INSTANCE.getEPackage(ProjectGenerationPackage.eNS_URI);

		// Obtain or create and register package
		ProjectGenerationPackageImpl theProjectGenerationPackage = (ProjectGenerationPackageImpl)(EPackage.Registry.INSTANCE.get(eNS_URI) instanceof ProjectGenerationPackageImpl ? EPackage.Registry.INSTANCE.get(eNS_URI) : new ProjectGenerationPackageImpl());

		isInited = true;

		// Create package meta-data objects
		theProjectGenerationPackage.createPackageContents();

		// Initialize created meta-data
		theProjectGenerationPackage.initializePackageContents();

		// Mark meta-data to indicate it can't be changed
		theProjectGenerationPackage.freeze();

  
		// Update the registry and return the package
		EPackage.Registry.INSTANCE.put(ProjectGenerationPackage.eNS_URI, theProjectGenerationPackage);
		return theProjectGenerationPackage;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EClass getProjectSettings() {
		return projectSettingsEClass;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EAttribute getProjectSettings_Name() {
		return (EAttribute)projectSettingsEClass.getEStructuralFeatures().get(0);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EAttribute getProjectSettings_SampleSet() {
		return (EAttribute)projectSettingsEClass.getEStructuralFeatures().get(1);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public EEnum getSampleSet() {
		return sampleSetEEnum;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public ProjectGenerationFactory getProjectGenerationFactory() {
		return (ProjectGenerationFactory)getEFactoryInstance();
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private boolean isCreated = false;

	/**
	 * Creates the meta-model objects for the package.  This method is
	 * guarded to have no affect on any invocation but its first.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public void createPackageContents() {
		if (isCreated) return;
		isCreated = true;

		// Create classes and their features
		projectSettingsEClass = createEClass(PROJECT_SETTINGS);
		createEAttribute(projectSettingsEClass, PROJECT_SETTINGS__NAME);
		createEAttribute(projectSettingsEClass, PROJECT_SETTINGS__SAMPLE_SET);

		// Create enums
		sampleSetEEnum = createEEnum(SAMPLE_SET);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private boolean isInitialized = false;

	/**
	 * Complete the initialization of the package and its meta-model.  This
	 * method is guarded to have no affect on any invocation but its first.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public void initializePackageContents() {
		if (isInitialized) return;
		isInitialized = true;

		// Initialize package
		setName(eNAME);
		setNsPrefix(eNS_PREFIX);
		setNsURI(eNS_URI);

		// Create type parameters

		// Set bounds for type parameters

		// Add supertypes to classes

		// Initialize classes and features; add operations and parameters
		initEClass(projectSettingsEClass, ProjectSettings.class, "ProjectSettings", !IS_ABSTRACT, !IS_INTERFACE, IS_GENERATED_INSTANCE_CLASS);
		initEAttribute(getProjectSettings_Name(), ecorePackage.getEString(), "name", null, 0, 1, ProjectSettings.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_UNSETTABLE, !IS_ID, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);
		initEAttribute(getProjectSettings_SampleSet(), this.getSampleSet(), "sampleSet", null, 0, 1, ProjectSettings.class, !IS_TRANSIENT, !IS_VOLATILE, IS_CHANGEABLE, !IS_UNSETTABLE, !IS_ID, IS_UNIQUE, !IS_DERIVED, IS_ORDERED);

		// Initialize enums and add enum literals
		initEEnum(sampleSetEEnum, SampleSet.class, "SampleSet");
		addEEnumLiteral(sampleSetEEnum, SampleSet.EMPTY);
		addEEnumLiteral(sampleSetEEnum, SampleSet.ARTICLE_2005);
		addEEnumLiteral(sampleSetEEnum, SampleSet.ACCOUNT_SIMPLE_CORE);
		addEEnumLiteral(sampleSetEEnum, SampleSet.ACCOUNT_COMPLEX_CORE);

		// Create resource
		createResource(eNS_URI);
	}

} //ProjectGenerationPackageImpl
