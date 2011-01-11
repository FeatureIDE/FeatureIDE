/**
 * <copyright>
 * </copyright>
 *
 */
package org.xtext.example.dJ;

import org.eclipse.emf.common.util.EList;

import org.eclipse.emf.ecore.EObject;

/**
 * <!-- begin-user-doc -->
 * A representation of the model object '<em><b>Configuration</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * <ul>
 *   <li>{@link org.xtext.example.dJ.Configuration#getFeatureList <em>Feature List</em>}</li>
 * </ul>
 * </p>
 *
 * @see org.xtext.example.dJ.DJPackage#getConfiguration()
 * @model
 * @generated
 */
public interface Configuration extends EObject
{
  /**
   * Returns the value of the '<em><b>Feature List</b></em>' containment reference list.
   * The list contents are of type {@link org.xtext.example.dJ.Config}.
   * <!-- begin-user-doc -->
   * <p>
   * If the meaning of the '<em>Feature List</em>' containment reference list isn't clear,
   * there really should be more of a description here...
   * </p>
   * <!-- end-user-doc -->
   * @return the value of the '<em>Feature List</em>' containment reference list.
   * @see org.xtext.example.dJ.DJPackage#getConfiguration_FeatureList()
   * @model containment="true"
   * @generated
   */
  EList<Config> getFeatureList();

} // Configuration
