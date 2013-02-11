/**
 * <copyright>
 * </copyright>
 *
 */
package org.xtext.example.dJ;

import org.eclipse.emf.ecore.EObject;

/**
 * <!-- begin-user-doc -->
 * A representation of the model object '<em><b>Renames Field</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * <ul>
 *   <li>{@link org.xtext.example.dJ.RenamesField#getFieldRef <em>Field Ref</em>}</li>
 *   <li>{@link org.xtext.example.dJ.RenamesField#getNewFieldRef <em>New Field Ref</em>}</li>
 * </ul>
 * </p>
 *
 * @see org.xtext.example.dJ.DJPackage#getRenamesField()
 * @model
 * @generated
 */
public interface RenamesField extends EObject
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
   * @see org.xtext.example.dJ.DJPackage#getRenamesField_FieldRef()
   * @model
   * @generated
   */
  FieldRef getFieldRef();

  /**
   * Sets the value of the '{@link org.xtext.example.dJ.RenamesField#getFieldRef <em>Field Ref</em>}' reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @param value the new value of the '<em>Field Ref</em>' reference.
   * @see #getFieldRef()
   * @generated
   */
  void setFieldRef(FieldRef value);

  /**
   * Returns the value of the '<em><b>New Field Ref</b></em>' containment reference.
   * <!-- begin-user-doc -->
   * <p>
   * If the meaning of the '<em>New Field Ref</em>' containment reference isn't clear,
   * there really should be more of a description here...
   * </p>
   * <!-- end-user-doc -->
   * @return the value of the '<em>New Field Ref</em>' containment reference.
   * @see #setNewFieldRef(FieldRef)
   * @see org.xtext.example.dJ.DJPackage#getRenamesField_NewFieldRef()
   * @model containment="true"
   * @generated
   */
  FieldRef getNewFieldRef();

  /**
   * Sets the value of the '{@link org.xtext.example.dJ.RenamesField#getNewFieldRef <em>New Field Ref</em>}' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @param value the new value of the '<em>New Field Ref</em>' containment reference.
   * @see #getNewFieldRef()
   * @generated
   */
  void setNewFieldRef(FieldRef value);

} // RenamesField
