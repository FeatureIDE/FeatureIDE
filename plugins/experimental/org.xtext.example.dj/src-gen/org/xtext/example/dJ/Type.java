/**
 * <copyright>
 * </copyright>
 *
 */
package org.xtext.example.dJ;

import org.eclipse.emf.ecore.EObject;

/**
 * <!-- begin-user-doc -->
 * A representation of the model object '<em><b>Type</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * <ul>
 *   <li>{@link org.xtext.example.dJ.Type#getBasic <em>Basic</em>}</li>
 *   <li>{@link org.xtext.example.dJ.Type#getClassref <em>Classref</em>}</li>
 * </ul>
 * </p>
 *
 * @see org.xtext.example.dJ.DJPackage#getType()
 * @model
 * @generated
 */
public interface Type extends EObject
{
  /**
   * Returns the value of the '<em><b>Basic</b></em>' attribute.
   * <!-- begin-user-doc -->
   * <p>
   * If the meaning of the '<em>Basic</em>' attribute isn't clear,
   * there really should be more of a description here...
   * </p>
   * <!-- end-user-doc -->
   * @return the value of the '<em>Basic</em>' attribute.
   * @see #setBasic(String)
   * @see org.xtext.example.dJ.DJPackage#getType_Basic()
   * @model
   * @generated
   */
  String getBasic();

  /**
   * Sets the value of the '{@link org.xtext.example.dJ.Type#getBasic <em>Basic</em>}' attribute.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @param value the new value of the '<em>Basic</em>' attribute.
   * @see #getBasic()
   * @generated
   */
  void setBasic(String value);

  /**
   * Returns the value of the '<em><b>Classref</b></em>' reference.
   * <!-- begin-user-doc -->
   * <p>
   * If the meaning of the '<em>Classref</em>' reference isn't clear,
   * there really should be more of a description here...
   * </p>
   * <!-- end-user-doc -->
   * @return the value of the '<em>Classref</em>' reference.
   * @see #setClassref(org.xtext.example.dJ.Class)
   * @see org.xtext.example.dJ.DJPackage#getType_Classref()
   * @model
   * @generated
   */
  org.xtext.example.dJ.Class getClassref();

  /**
   * Sets the value of the '{@link org.xtext.example.dJ.Type#getClassref <em>Classref</em>}' reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @param value the new value of the '<em>Classref</em>' reference.
   * @see #getClassref()
   * @generated
   */
  void setClassref(org.xtext.example.dJ.Class value);

} // Type
