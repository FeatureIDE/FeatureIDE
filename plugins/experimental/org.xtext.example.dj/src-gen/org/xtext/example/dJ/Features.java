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
 * A representation of the model object '<em><b>Features</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * <ul>
 *   <li>{@link org.xtext.example.dJ.Features#getFeaturesList <em>Features List</em>}</li>
 *   <li>{@link org.xtext.example.dJ.Features#getConfiguration <em>Configuration</em>}</li>
 * </ul>
 * </p>
 *
 * @see org.xtext.example.dJ.DJPackage#getFeatures()
 * @model
 * @generated
 */
public interface Features extends EObject
{
  /**
   * Returns the value of the '<em><b>Features List</b></em>' containment reference list.
   * The list contents are of type {@link org.xtext.example.dJ.Feature}.
   * <!-- begin-user-doc -->
   * <p>
   * If the meaning of the '<em>Features List</em>' containment reference list isn't clear,
   * there really should be more of a description here...
   * </p>
   * <!-- end-user-doc -->
   * @return the value of the '<em>Features List</em>' containment reference list.
   * @see org.xtext.example.dJ.DJPackage#getFeatures_FeaturesList()
   * @model containment="true"
   * @generated
   */
  EList<Feature> getFeaturesList();

  /**
   * Returns the value of the '<em><b>Configuration</b></em>' containment reference.
   * <!-- begin-user-doc -->
   * <p>
   * If the meaning of the '<em>Configuration</em>' containment reference isn't clear,
   * there really should be more of a description here...
   * </p>
   * <!-- end-user-doc -->
   * @return the value of the '<em>Configuration</em>' containment reference.
   * @see #setConfiguration(Configuration)
   * @see org.xtext.example.dJ.DJPackage#getFeatures_Configuration()
   * @model containment="true"
   * @generated
   */
  Configuration getConfiguration();

  /**
   * Sets the value of the '{@link org.xtext.example.dJ.Features#getConfiguration <em>Configuration</em>}' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @param value the new value of the '<em>Configuration</em>' containment reference.
   * @see #getConfiguration()
   * @generated
   */
  void setConfiguration(Configuration value);

} // Features
