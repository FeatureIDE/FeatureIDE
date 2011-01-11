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
 * A representation of the model object '<em><b>Methodm</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * <ul>
 *   <li>{@link org.xtext.example.dJ.Methodm#getRemoveList <em>Remove List</em>}</li>
 *   <li>{@link org.xtext.example.dJ.Methodm#getModifiesList <em>Modifies List</em>}</li>
 *   <li>{@link org.xtext.example.dJ.Methodm#getAddsList <em>Adds List</em>}</li>
 * </ul>
 * </p>
 *
 * @see org.xtext.example.dJ.DJPackage#getMethodm()
 * @model
 * @generated
 */
public interface Methodm extends EObject
{
  /**
   * Returns the value of the '<em><b>Remove List</b></em>' containment reference list.
   * The list contents are of type {@link org.xtext.example.dJ.RemovesMethod}.
   * <!-- begin-user-doc -->
   * <p>
   * If the meaning of the '<em>Remove List</em>' containment reference list isn't clear,
   * there really should be more of a description here...
   * </p>
   * <!-- end-user-doc -->
   * @return the value of the '<em>Remove List</em>' containment reference list.
   * @see org.xtext.example.dJ.DJPackage#getMethodm_RemoveList()
   * @model containment="true"
   * @generated
   */
  EList<RemovesMethod> getRemoveList();

  /**
   * Returns the value of the '<em><b>Modifies List</b></em>' containment reference list.
   * The list contents are of type {@link org.xtext.example.dJ.ModifiesMethod}.
   * <!-- begin-user-doc -->
   * <p>
   * If the meaning of the '<em>Modifies List</em>' containment reference list isn't clear,
   * there really should be more of a description here...
   * </p>
   * <!-- end-user-doc -->
   * @return the value of the '<em>Modifies List</em>' containment reference list.
   * @see org.xtext.example.dJ.DJPackage#getMethodm_ModifiesList()
   * @model containment="true"
   * @generated
   */
  EList<ModifiesMethod> getModifiesList();

  /**
   * Returns the value of the '<em><b>Adds List</b></em>' containment reference list.
   * The list contents are of type {@link org.xtext.example.dJ.AddsMethod}.
   * <!-- begin-user-doc -->
   * <p>
   * If the meaning of the '<em>Adds List</em>' containment reference list isn't clear,
   * there really should be more of a description here...
   * </p>
   * <!-- end-user-doc -->
   * @return the value of the '<em>Adds List</em>' containment reference list.
   * @see org.xtext.example.dJ.DJPackage#getMethodm_AddsList()
   * @model containment="true"
   * @generated
   */
  EList<AddsMethod> getAddsList();

} // Methodm
