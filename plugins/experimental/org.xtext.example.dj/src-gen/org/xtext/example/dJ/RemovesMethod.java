/**
 * <copyright>
 * </copyright>
 *
 */
package org.xtext.example.dJ;

import org.eclipse.emf.ecore.EObject;

/**
 * <!-- begin-user-doc -->
 * A representation of the model object '<em><b>Removes Method</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * <ul>
 *   <li>{@link org.xtext.example.dJ.RemovesMethod#getMethodRef <em>Method Ref</em>}</li>
 * </ul>
 * </p>
 *
 * @see org.xtext.example.dJ.DJPackage#getRemovesMethod()
 * @model
 * @generated
 */
public interface RemovesMethod extends EObject
{
  /**
   * Returns the value of the '<em><b>Method Ref</b></em>' reference.
   * <!-- begin-user-doc -->
   * <p>
   * If the meaning of the '<em>Method Ref</em>' reference isn't clear,
   * there really should be more of a description here...
   * </p>
   * <!-- end-user-doc -->
   * @return the value of the '<em>Method Ref</em>' reference.
   * @see #setMethodRef(MethodRef)
   * @see org.xtext.example.dJ.DJPackage#getRemovesMethod_MethodRef()
   * @model
   * @generated
   */
  MethodRef getMethodRef();

  /**
   * Sets the value of the '{@link org.xtext.example.dJ.RemovesMethod#getMethodRef <em>Method Ref</em>}' reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @param value the new value of the '<em>Method Ref</em>' reference.
   * @see #getMethodRef()
   * @generated
   */
  void setMethodRef(MethodRef value);

} // RemovesMethod
