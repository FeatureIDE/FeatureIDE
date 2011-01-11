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
 * A representation of the model object '<em><b>Delta</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * <ul>
 *   <li>{@link org.xtext.example.dJ.Delta#getName <em>Name</em>}</li>
 *   <li>{@link org.xtext.example.dJ.Delta#getAfter <em>After</em>}</li>
 *   <li>{@link org.xtext.example.dJ.Delta#getCondition <em>Condition</em>}</li>
 *   <li>{@link org.xtext.example.dJ.Delta#getClassesList <em>Classes List</em>}</li>
 * </ul>
 * </p>
 *
 * @see org.xtext.example.dJ.DJPackage#getDelta()
 * @model
 * @generated
 */
public interface Delta extends EObject
{
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
   * @see org.xtext.example.dJ.DJPackage#getDelta_Name()
   * @model
   * @generated
   */
  String getName();

  /**
   * Sets the value of the '{@link org.xtext.example.dJ.Delta#getName <em>Name</em>}' attribute.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @param value the new value of the '<em>Name</em>' attribute.
   * @see #getName()
   * @generated
   */
  void setName(String value);

  /**
   * Returns the value of the '<em><b>After</b></em>' reference list.
   * The list contents are of type {@link org.xtext.example.dJ.Delta}.
   * <!-- begin-user-doc -->
   * <p>
   * If the meaning of the '<em>After</em>' reference list isn't clear,
   * there really should be more of a description here...
   * </p>
   * <!-- end-user-doc -->
   * @return the value of the '<em>After</em>' reference list.
   * @see org.xtext.example.dJ.DJPackage#getDelta_After()
   * @model
   * @generated
   */
  EList<Delta> getAfter();

  /**
   * Returns the value of the '<em><b>Condition</b></em>' containment reference list.
   * The list contents are of type {@link org.xtext.example.dJ.Condition}.
   * <!-- begin-user-doc -->
   * <p>
   * If the meaning of the '<em>Condition</em>' containment reference list isn't clear,
   * there really should be more of a description here...
   * </p>
   * <!-- end-user-doc -->
   * @return the value of the '<em>Condition</em>' containment reference list.
   * @see org.xtext.example.dJ.DJPackage#getDelta_Condition()
   * @model containment="true"
   * @generated
   */
  EList<Condition> getCondition();

  /**
   * Returns the value of the '<em><b>Classes List</b></em>' containment reference list.
   * The list contents are of type {@link org.xtext.example.dJ.Classm}.
   * <!-- begin-user-doc -->
   * <p>
   * If the meaning of the '<em>Classes List</em>' containment reference list isn't clear,
   * there really should be more of a description here...
   * </p>
   * <!-- end-user-doc -->
   * @return the value of the '<em>Classes List</em>' containment reference list.
   * @see org.xtext.example.dJ.DJPackage#getDelta_ClassesList()
   * @model containment="true"
   * @generated
   */
  EList<Classm> getClassesList();

} // Delta
