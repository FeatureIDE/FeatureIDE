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
 * A representation of the model object '<em><b>Modifies Method</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * <ul>
 *   <li>{@link org.xtext.example.dJ.ModifiesMethod#getReturntype <em>Returntype</em>}</li>
 *   <li>{@link org.xtext.example.dJ.ModifiesMethod#getMethodRef <em>Method Ref</em>}</li>
 *   <li>{@link org.xtext.example.dJ.ModifiesMethod#getParams <em>Params</em>}</li>
 *   <li>{@link org.xtext.example.dJ.ModifiesMethod#getBody <em>Body</em>}</li>
 * </ul>
 * </p>
 *
 * @see org.xtext.example.dJ.DJPackage#getModifiesMethod()
 * @model
 * @generated
 */
public interface ModifiesMethod extends EObject
{
  /**
   * Returns the value of the '<em><b>Returntype</b></em>' containment reference.
   * <!-- begin-user-doc -->
   * <p>
   * If the meaning of the '<em>Returntype</em>' containment reference isn't clear,
   * there really should be more of a description here...
   * </p>
   * <!-- end-user-doc -->
   * @return the value of the '<em>Returntype</em>' containment reference.
   * @see #setReturntype(Type)
   * @see org.xtext.example.dJ.DJPackage#getModifiesMethod_Returntype()
   * @model containment="true"
   * @generated
   */
  Type getReturntype();

  /**
   * Sets the value of the '{@link org.xtext.example.dJ.ModifiesMethod#getReturntype <em>Returntype</em>}' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @param value the new value of the '<em>Returntype</em>' containment reference.
   * @see #getReturntype()
   * @generated
   */
  void setReturntype(Type value);

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
   * @see org.xtext.example.dJ.DJPackage#getModifiesMethod_MethodRef()
   * @model
   * @generated
   */
  MethodRef getMethodRef();

  /**
   * Sets the value of the '{@link org.xtext.example.dJ.ModifiesMethod#getMethodRef <em>Method Ref</em>}' reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @param value the new value of the '<em>Method Ref</em>' reference.
   * @see #getMethodRef()
   * @generated
   */
  void setMethodRef(MethodRef value);

  /**
   * Returns the value of the '<em><b>Params</b></em>' containment reference list.
   * The list contents are of type {@link org.xtext.example.dJ.Parameter}.
   * <!-- begin-user-doc -->
   * <p>
   * If the meaning of the '<em>Params</em>' containment reference list isn't clear,
   * there really should be more of a description here...
   * </p>
   * <!-- end-user-doc -->
   * @return the value of the '<em>Params</em>' containment reference list.
   * @see org.xtext.example.dJ.DJPackage#getModifiesMethod_Params()
   * @model containment="true"
   * @generated
   */
  EList<Parameter> getParams();

  /**
   * Returns the value of the '<em><b>Body</b></em>' containment reference.
   * <!-- begin-user-doc -->
   * <p>
   * If the meaning of the '<em>Body</em>' containment reference isn't clear,
   * there really should be more of a description here...
   * </p>
   * <!-- end-user-doc -->
   * @return the value of the '<em>Body</em>' containment reference.
   * @see #setBody(MethodBody)
   * @see org.xtext.example.dJ.DJPackage#getModifiesMethod_Body()
   * @model containment="true"
   * @generated
   */
  MethodBody getBody();

  /**
   * Sets the value of the '{@link org.xtext.example.dJ.ModifiesMethod#getBody <em>Body</em>}' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @param value the new value of the '<em>Body</em>' containment reference.
   * @see #getBody()
   * @generated
   */
  void setBody(MethodBody value);

} // ModifiesMethod
