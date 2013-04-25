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
 * A representation of the model object '<em><b>Features</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * <ul>
 *   <li>{@link org.deltaj.deltaj.Features#getFeaturesList <em>Features List</em>}</li>
 * </ul>
 * </p>
 *
 * @see org.deltaj.deltaj.DeltajPackage#getFeatures()
 * @model
 * @generated
 */
public interface Features extends EObject
{
  /**
   * Returns the value of the '<em><b>Features List</b></em>' containment reference list.
   * The list contents are of type {@link org.deltaj.deltaj.Feature}.
   * <!-- begin-user-doc -->
   * <p>
   * If the meaning of the '<em>Features List</em>' containment reference list isn't clear,
   * there really should be more of a description here...
   * </p>
   * <!-- end-user-doc -->
   * @return the value of the '<em>Features List</em>' containment reference list.
   * @see org.deltaj.deltaj.DeltajPackage#getFeatures_FeaturesList()
   * @model containment="true"
   * @generated
   */
  EList<Feature> getFeaturesList();

} // Features
