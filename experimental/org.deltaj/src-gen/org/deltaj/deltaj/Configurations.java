/**
 * <copyright>
 * </copyright>
 *
 */
package org.deltaj.deltaj;

import org.eclipse.emf.common.util.EList;

import org.eclipse.emf.ecore.EObject;

/**
 * <!-- begin-user-doc -->
 * A representation of the model object '<em><b>Configurations</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * <ul>
 *   <li>{@link org.deltaj.deltaj.Configurations#getConfigurations <em>Configurations</em>}</li>
 * </ul>
 * </p>
 *
 * @see org.deltaj.deltaj.DeltajPackage#getConfigurations()
 * @model
 * @generated
 */
public interface Configurations extends EObject
{
  /**
   * Returns the value of the '<em><b>Configurations</b></em>' containment reference list.
   * The list contents are of type {@link org.deltaj.deltaj.Configuration}.
   * <!-- begin-user-doc -->
   * <p>
   * If the meaning of the '<em>Configurations</em>' containment reference list isn't clear,
   * there really should be more of a description here...
   * </p>
   * <!-- end-user-doc -->
   * @return the value of the '<em>Configurations</em>' containment reference list.
   * @see org.deltaj.deltaj.DeltajPackage#getConfigurations_Configurations()
   * @model containment="true"
   * @generated
   */
  EList<Configuration> getConfigurations();

} // Configurations
