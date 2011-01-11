/**
 * <copyright>
 * </copyright>
 *
 */
package org.xtext.example.dJ;

import org.eclipse.emf.ecore.EObject;

/**
 * <!-- begin-user-doc -->
 * A representation of the model object '<em><b>Adds Method</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * <ul>
 *   <li>{@link org.xtext.example.dJ.AddsMethod#getMethod <em>Method</em>}</li>
 * </ul>
 * </p>
 *
 * @see org.xtext.example.dJ.DJPackage#getAddsMethod()
 * @model
 * @generated
 */
public interface AddsMethod extends EObject
{
  /**
   * Returns the value of the '<em><b>Method</b></em>' containment reference.
   * <!-- begin-user-doc -->
   * <p>
   * If the meaning of the '<em>Method</em>' containment reference isn't clear,
   * there really should be more of a description here...
   * </p>
   * <!-- end-user-doc -->
   * @return the value of the '<em>Method</em>' containment reference.
   * @see #setMethod(Method)
   * @see org.xtext.example.dJ.DJPackage#getAddsMethod_Method()
   * @model containment="true"
   * @generated
   */
  Method getMethod();

  /**
   * Sets the value of the '{@link org.xtext.example.dJ.AddsMethod#getMethod <em>Method</em>}' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @param value the new value of the '<em>Method</em>' containment reference.
   * @see #getMethod()
   * @generated
   */
  void setMethod(Method value);

} // AddsMethod
