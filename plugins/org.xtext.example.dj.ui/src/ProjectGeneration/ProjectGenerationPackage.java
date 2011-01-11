/**
 * <copyright>
 * </copyright>
 *
 * $Id$
 */
package ProjectGeneration;

import org.eclipse.emf.ecore.EAttribute;
import org.eclipse.emf.ecore.EClass;
import org.eclipse.emf.ecore.EEnum;
import org.eclipse.emf.ecore.EPackage;

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
 * @see ProjectGeneration.ProjectGenerationFactory
 * @model kind="package"
 * @generated
 */
public interface ProjectGenerationPackage extends EPackage {
	/**
	 * The package name.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	String eNAME = "ProjectGeneration";

	/**
	 * The package namespace URI.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	String eNS_URI = "http://www.xtext.org/example/mydsl/ui/DJProject";

	/**
	 * The package namespace name.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	String eNS_PREFIX = "ProjectGeneration";

	/**
	 * The singleton instance of the package.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	ProjectGenerationPackage eINSTANCE = ProjectGeneration.impl.ProjectGenerationPackageImpl.init();

	/**
	 * The meta object id for the '{@link ProjectGeneration.impl.ProjectSettingsImpl <em>Project Settings</em>}' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see ProjectGeneration.impl.ProjectSettingsImpl
	 * @see ProjectGeneration.impl.ProjectGenerationPackageImpl#getProjectSettings()
	 * @generated
	 */
	int PROJECT_SETTINGS = 0;

	/**
	 * The feature id for the '<em><b>Name</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int PROJECT_SETTINGS__NAME = 0;

	/**
	 * The feature id for the '<em><b>Sample Set</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int PROJECT_SETTINGS__SAMPLE_SET = 1;

	/**
	 * The number of structural features of the '<em>Project Settings</em>' class.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 * @ordered
	 */
	int PROJECT_SETTINGS_FEATURE_COUNT = 2;

	/**
	 * The meta object id for the '{@link ProjectGeneration.SampleSet <em>Sample Set</em>}' enum.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see ProjectGeneration.SampleSet
	 * @see ProjectGeneration.impl.ProjectGenerationPackageImpl#getSampleSet()
	 * @generated
	 */
	int SAMPLE_SET = 1;


	/**
	 * Returns the meta object for class '{@link ProjectGeneration.ProjectSettings <em>Project Settings</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for class '<em>Project Settings</em>'.
	 * @see ProjectGeneration.ProjectSettings
	 * @generated
	 */
	EClass getProjectSettings();

	/**
	 * Returns the meta object for the attribute '{@link ProjectGeneration.ProjectSettings#getName <em>Name</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute '<em>Name</em>'.
	 * @see ProjectGeneration.ProjectSettings#getName()
	 * @see #getProjectSettings()
	 * @generated
	 */
	EAttribute getProjectSettings_Name();

	/**
	 * Returns the meta object for the attribute '{@link ProjectGeneration.ProjectSettings#getSampleSet <em>Sample Set</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for the attribute '<em>Sample Set</em>'.
	 * @see ProjectGeneration.ProjectSettings#getSampleSet()
	 * @see #getProjectSettings()
	 * @generated
	 */
	EAttribute getProjectSettings_SampleSet();

	/**
	 * Returns the meta object for enum '{@link ProjectGeneration.SampleSet <em>Sample Set</em>}'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the meta object for enum '<em>Sample Set</em>'.
	 * @see ProjectGeneration.SampleSet
	 * @generated
	 */
	EEnum getSampleSet();

	/**
	 * Returns the factory that creates the instances of the model.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the factory that creates the instances of the model.
	 * @generated
	 */
	ProjectGenerationFactory getProjectGenerationFactory();

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
	interface Literals {
		/**
		 * The meta object literal for the '{@link ProjectGeneration.impl.ProjectSettingsImpl <em>Project Settings</em>}' class.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see ProjectGeneration.impl.ProjectSettingsImpl
		 * @see ProjectGeneration.impl.ProjectGenerationPackageImpl#getProjectSettings()
		 * @generated
		 */
		EClass PROJECT_SETTINGS = eINSTANCE.getProjectSettings();

		/**
		 * The meta object literal for the '<em><b>Name</b></em>' attribute feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EAttribute PROJECT_SETTINGS__NAME = eINSTANCE.getProjectSettings_Name();

		/**
		 * The meta object literal for the '<em><b>Sample Set</b></em>' attribute feature.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @generated
		 */
		EAttribute PROJECT_SETTINGS__SAMPLE_SET = eINSTANCE.getProjectSettings_SampleSet();

		/**
		 * The meta object literal for the '{@link ProjectGeneration.SampleSet <em>Sample Set</em>}' enum.
		 * <!-- begin-user-doc -->
		 * <!-- end-user-doc -->
		 * @see ProjectGeneration.SampleSet
		 * @see ProjectGeneration.impl.ProjectGenerationPackageImpl#getSampleSet()
		 * @generated
		 */
		EEnum SAMPLE_SET = eINSTANCE.getSampleSet();

	}

} //ProjectGenerationPackage
