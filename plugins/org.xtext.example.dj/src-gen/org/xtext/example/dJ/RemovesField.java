/**
 * <copyright>
 * </copyright>
 *
 */
package org.xtext.example.dJ;

import org.eclipse.emf.ecore.EObject;

/**
 * <!-- begin-user-doc -->
 * A representation of the model object '<em><b>Removes Field</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * <ul>
 *   <li>{@link org.xtext.example.dJ.RemovesField#getFieldRef <em>Field Ref</em>}</li>
 * </ul>
 * </p>
 *
 * @see org.xtext.example.dJ.DJPackage#getRemovesField()
 * @model
 * @generated
 */
public interface RemovesField extends EObject
{
  /**
   * Returns the value of the '<em><b>Field Ref</b></em>' reference.
   * <!-- begin-user-doc -->
   * <p>
   * If the meaning of the '<em>Field Ref</em>' reference isn't clear,
   * there really should be more of a description here...
   * </p>
   * <!-- end-user-doc -->
   * @return the value of the '<em>Field Ref</em>' reference.
   * @see #setFieldRef(FieldRef)
   * @see org.xtext.example.dJ.DJPackage#getRemovesField_FieldRef()
   * @model
   * @generated
   */
  FieldRef getFieldRef();

  /**
   * Sets the value of the '{@link org.xtext.example.dJ.RemovesField#getFieldRef <em>Field Ref</em>}' reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @param value the new value of the '<em>Field Ref</em>' reference.
   * @see #getFieldRef()
   * @generated
   */
  void setFieldRef(FieldRef value);

} // RemovesField
