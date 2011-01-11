/**
 * <copyright>
 * </copyright>
 *
 */
package org.xtext.example.dJ;

import org.eclipse.emf.ecore.EObject;

/**
 * <!-- begin-user-doc -->
 * A representation of the model object '<em><b>Variable</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * <ul>
 *   <li>{@link org.xtext.example.dJ.Variable#getParameter <em>Parameter</em>}</li>
 *   <li>{@link org.xtext.example.dJ.Variable#getFieldRef <em>Field Ref</em>}</li>
 * </ul>
 * </p>
 *
 * @see org.xtext.example.dJ.DJPackage#getVariable()
 * @model
 * @generated
 */
public interface Variable extends EObject
{
  /**
   * Returns the value of the '<em><b>Parameter</b></em>' reference.
   * <!-- begin-user-doc -->
   * <p>
   * If the meaning of the '<em>Parameter</em>' reference isn't clear,
   * there really should be more of a description here...
   * </p>
   * <!-- end-user-doc -->
   * @return the value of the '<em>Parameter</em>' reference.
   * @see #setParameter(Parameter)
   * @see org.xtext.example.dJ.DJPackage#getVariable_Parameter()
   * @model
   * @generated
   */
  Parameter getParameter();

  /**
   * Sets the value of the '{@link org.xtext.example.dJ.Variable#getParameter <em>Parameter</em>}' reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @param value the new value of the '<em>Parameter</em>' reference.
   * @see #getParameter()
   * @generated
   */
  void setParameter(Parameter value);

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
   * @see org.xtext.example.dJ.DJPackage#getVariable_FieldRef()
   * @model
   * @generated
   */
  FieldRef getFieldRef();

  /**
   * Sets the value of the '{@link org.xtext.example.dJ.Variable#getFieldRef <em>Field Ref</em>}' reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @param value the new value of the '<em>Field Ref</em>' reference.
   * @see #getFieldRef()
   * @generated
   */
  void setFieldRef(FieldRef value);

} // Variable
