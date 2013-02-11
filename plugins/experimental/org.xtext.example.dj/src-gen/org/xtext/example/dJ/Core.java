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
 * A representation of the model object '<em><b>Core</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * <ul>
 *   <li>{@link org.xtext.example.dJ.Core#getName <em>Name</em>}</li>
 *   <li>{@link org.xtext.example.dJ.Core#getClassesList <em>Classes List</em>}</li>
 * </ul>
 * </p>
 *
 * @see org.xtext.example.dJ.DJPackage#getCore()
 * @model
 * @generated
 */
public interface Core extends EObject
{
  /**
   * Returns the value of the '<em><b>Name</b></em>' reference list.
   * The list contents are of type {@link org.xtext.example.dJ.Feature}.
   * <!-- begin-user-doc -->
   * <p>
   * If the meaning of the '<em>Name</em>' reference list isn't clear,
   * there really should be more of a description here...
   * </p>
   * <!-- end-user-doc -->
   * @return the value of the '<em>Name</em>' reference list.
   * @see org.xtext.example.dJ.DJPackage#getCore_Name()
   * @model
   * @generated
   */
  EList<Feature> getName();

  /**
   * Returns the value of the '<em><b>Classes List</b></em>' containment reference list.
   * The list contents are of type {@link org.xtext.example.dJ.Class}.
   * <!-- begin-user-doc -->
   * <p>
   * If the meaning of the '<em>Classes List</em>' containment reference list isn't clear,
   * there really should be more of a description here...
   * </p>
   * <!-- end-user-doc -->
   * @return the value of the '<em>Classes List</em>' containment reference list.
   * @see org.xtext.example.dJ.DJPackage#getCore_ClassesList()
   * @model containment="true"
   * @generated
   */
  EList<org.xtext.example.dJ.Class> getClassesList();

} // Core
