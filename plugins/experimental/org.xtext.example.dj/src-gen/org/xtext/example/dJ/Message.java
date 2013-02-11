/**
 * <copyright>
 * </copyright>
 *
 */
package org.xtext.example.dJ;

import org.eclipse.emf.ecore.EObject;

/**
 * <!-- begin-user-doc -->
 * A representation of the model object '<em><b>Message</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * <ul>
 *   <li>{@link org.xtext.example.dJ.Message#getMethodCall <em>Method Call</em>}</li>
 *   <li>{@link org.xtext.example.dJ.Message#getFieldAccess <em>Field Access</em>}</li>
 * </ul>
 * </p>
 *
 * @see org.xtext.example.dJ.DJPackage#getMessage()
 * @model
 * @generated
 */
public interface Message extends EObject
{
  /**
   * Returns the value of the '<em><b>Method Call</b></em>' containment reference.
   * <!-- begin-user-doc -->
   * <p>
   * If the meaning of the '<em>Method Call</em>' containment reference isn't clear,
   * there really should be more of a description here...
   * </p>
   * <!-- end-user-doc -->
   * @return the value of the '<em>Method Call</em>' containment reference.
   * @see #setMethodCall(MethodCall)
   * @see org.xtext.example.dJ.DJPackage#getMessage_MethodCall()
   * @model containment="true"
   * @generated
   */
  MethodCall getMethodCall();

  /**
   * Sets the value of the '{@link org.xtext.example.dJ.Message#getMethodCall <em>Method Call</em>}' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @param value the new value of the '<em>Method Call</em>' containment reference.
   * @see #getMethodCall()
   * @generated
   */
  void setMethodCall(MethodCall value);

  /**
   * Returns the value of the '<em><b>Field Access</b></em>' containment reference.
   * <!-- begin-user-doc -->
   * <p>
   * If the meaning of the '<em>Field Access</em>' containment reference isn't clear,
   * there really should be more of a description here...
   * </p>
   * <!-- end-user-doc -->
   * @return the value of the '<em>Field Access</em>' containment reference.
   * @see #setFieldAccess(FieldAccess)
   * @see org.xtext.example.dJ.DJPackage#getMessage_FieldAccess()
   * @model containment="true"
   * @generated
   */
  FieldAccess getFieldAccess();

  /**
   * Sets the value of the '{@link org.xtext.example.dJ.Message#getFieldAccess <em>Field Access</em>}' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @param value the new value of the '<em>Field Access</em>' containment reference.
   * @see #getFieldAccess()
   * @generated
   */
  void setFieldAccess(FieldAccess value);

} // Message
