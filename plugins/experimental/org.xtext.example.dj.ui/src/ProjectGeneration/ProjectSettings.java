/**
 * <copyright>
 * </copyright>
 *
 * $Id$
 */
package ProjectGeneration;

import org.eclipse.emf.ecore.EObject;

/**
 * <!-- begin-user-doc -->
 * A representation of the model object '<em><b>Project Settings</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * <ul>
 *   <li>{@link ProjectGeneration.ProjectSettings#getName <em>Name</em>}</li>
 *   <li>{@link ProjectGeneration.ProjectSettings#getSampleSet <em>Sample Set</em>}</li>
 * </ul>
 * </p>
 *
 * @see ProjectGeneration.ProjectGenerationPackage#getProjectSettings()
 * @model
 * @generated
 */
public interface ProjectSettings extends EObject {
	/**
	 * Returns the value of the '<em><b>Name</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <p>
	 * If the meaning of the '<em>Name</em>' attribute isn't clear,
	 * there really should be more of a description here...
	 * </p>
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Name</em>' attribute.
	 * @see #setName(String)
	 * @see ProjectGeneration.ProjectGenerationPackage#getProjectSettings_Name()
	 * @model
	 * @generated
	 */
	String getName();

	/**
	 * Sets the value of the '{@link ProjectGeneration.ProjectSettings#getName <em>Name</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Name</em>' attribute.
	 * @see #getName()
	 * @generated
	 */
	void setName(String value);

	/**
	 * Returns the value of the '<em><b>Sample Set</b></em>' attribute.
	 * The literals are from the enumeration {@link ProjectGeneration.SampleSet}.
	 * <!-- begin-user-doc -->
	 * <p>
	 * If the meaning of the '<em>Sample Set</em>' attribute isn't clear,
	 * there really should be more of a description here...
	 * </p>
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Sample Set</em>' attribute.
	 * @see ProjectGeneration.SampleSet
	 * @see #setSampleSet(SampleSet)
	 * @see ProjectGeneration.ProjectGenerationPackage#getProjectSettings_SampleSet()
	 * @model
	 * @generated
	 */
	SampleSet getSampleSet();

	/**
	 * Sets the value of the '{@link ProjectGeneration.ProjectSettings#getSampleSet <em>Sample Set</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Sample Set</em>' attribute.
	 * @see ProjectGeneration.SampleSet
	 * @see #getSampleSet()
	 * @generated
	 */
	void setSampleSet(SampleSet value);

} // ProjectSettings
