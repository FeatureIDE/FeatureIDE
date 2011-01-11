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
 * A representation of the model object '<em><b>Fieldm</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * <ul>
 *   <li>{@link org.xtext.example.dJ.Fieldm#getRemoveList <em>Remove List</em>}</li>
 *   <li>{@link org.xtext.example.dJ.Fieldm#getAddsList <em>Adds List</em>}</li>
 * </ul>
 * </p>
 *
 * @see org.xtext.example.dJ.DJPackage#getFieldm()
 * @model
 * @generated
 */
public interface Fieldm extends EObject
{
  /**
   * Returns the value of the '<em><b>Remove List</b></em>' containment reference list.
   * The list contents are of type {@link org.xtext.example.dJ.RemovesField}.
   * <!-- begin-user-doc -->
   * <p>
   * If the meaning of the '<em>Remove List</em>' containment reference list isn't clear,
   * there really should be more of a description here...
   * </p>
   * <!-- end-user-doc -->
   * @return the value of the '<em>Remove List</em>' containment reference list.
   * @see org.xtext.example.dJ.DJPackage#getFieldm_RemoveList()
   * @model containment="true"
   * @generated
   */
  EList<RemovesField> getRemoveList();

  /**
   * Returns the value of the '<em><b>Adds List</b></em>' containment reference list.
   * The list contents are of type {@link org.xtext.example.dJ.AddsField}.
   * <!-- begin-user-doc -->
   * <p>
   * If the meaning of the '<em>Adds List</em>' containment reference list isn't clear,
   * there really should be more of a description here...
   * </p>
   * <!-- end-user-doc -->
   * @return the value of the '<em>Adds List</em>' containment reference list.
   * @see org.xtext.example.dJ.DJPackage#getFieldm_AddsList()
   * @model containment="true"
   * @generated
   */
  EList<AddsField> getAddsList();

} // Fieldm
