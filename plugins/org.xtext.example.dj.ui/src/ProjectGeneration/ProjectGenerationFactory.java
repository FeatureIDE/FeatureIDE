/**
 * <copyright>
 * </copyright>
 *
 * $Id$
 */
package ProjectGeneration;

import org.eclipse.emf.ecore.EFactory;

/**
 * <!-- begin-user-doc -->
 * The <b>Factory</b> for the model.
 * It provides a create method for each non-abstract class of the model.
 * <!-- end-user-doc -->
 * @see ProjectGeneration.ProjectGenerationPackage
 * @generated
 */
public interface ProjectGenerationFactory extends EFactory {
	/**
	 * The singleton instance of the factory.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	ProjectGenerationFactory eINSTANCE = ProjectGeneration.impl.ProjectGenerationFactoryImpl.init();

	/**
	 * Returns a new object of class '<em>Project Settings</em>'.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return a new object of class '<em>Project Settings</em>'.
	 * @generated
	 */
	ProjectSettings createProjectSettings();

	/**
	 * Returns the package supported by this factory.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the package supported by this factory.
	 * @generated
	 */
	ProjectGenerationPackage getProjectGenerationPackage();

} //ProjectGenerationFactory
