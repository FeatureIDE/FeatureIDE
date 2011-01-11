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
 * A representation of the model object '<em><b>Constructor</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * <ul>
 *   <li>{@link org.xtext.example.dJ.Constructor#getName <em>Name</em>}</li>
 *   <li>{@link org.xtext.example.dJ.Constructor#getParams <em>Params</em>}</li>
 *   <li>{@link org.xtext.example.dJ.Constructor#getConstructorSuperExpression <em>Constructor Super Expression</em>}</li>
 *   <li>{@link org.xtext.example.dJ.Constructor#getConstructorFieldExpression <em>Constructor Field Expression</em>}</li>
 * </ul>
 * </p>
 *
 * @see org.xtext.example.dJ.DJPackage#getConstructor()
 * @model
 * @generated
 */
public interface Constructor extends EObject
{
  /**
   * Returns the value of the '<em><b>Name</b></em>' reference.
   * <!-- begin-user-doc -->
   * <p>
   * If the meaning of the '<em>Name</em>' reference isn't clear,
   * there really should be more of a description here...
   * </p>
   * <!-- end-user-doc -->
   * @return the value of the '<em>Name</em>' reference.
   * @see #setName(org.xtext.example.dJ.Class)
   * @see org.xtext.example.dJ.DJPackage#getConstructor_Name()
   * @model
   * @generated
   */
  org.xtext.example.dJ.Class getName();

  /**
   * Sets the value of the '{@link org.xtext.example.dJ.Constructor#getName <em>Name</em>}' reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @param value the new value of the '<em>Name</em>' reference.
   * @see #getName()
   * @generated
   */
  void setName(org.xtext.example.dJ.Class value);

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
   * @see org.xtext.example.dJ.DJPackage#getConstructor_Params()
   * @model containment="true"
   * @generated
   */
  EList<Parameter> getParams();

  /**
   * Returns the value of the '<em><b>Constructor Super Expression</b></em>' containment reference.
   * <!-- begin-user-doc -->
   * <p>
   * If the meaning of the '<em>Constructor Super Expression</em>' containment reference isn't clear,
   * there really should be more of a description here...
   * </p>
   * <!-- end-user-doc -->
   * @return the value of the '<em>Constructor Super Expression</em>' containment reference.
   * @see #setConstructorSuperExpression(ConstructorSuperExpression)
   * @see org.xtext.example.dJ.DJPackage#getConstructor_ConstructorSuperExpression()
   * @model containment="true"
   * @generated
   */
  ConstructorSuperExpression getConstructorSuperExpression();

  /**
   * Sets the value of the '{@link org.xtext.example.dJ.Constructor#getConstructorSuperExpression <em>Constructor Super Expression</em>}' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @param value the new value of the '<em>Constructor Super Expression</em>' containment reference.
   * @see #getConstructorSuperExpression()
   * @generated
   */
  void setConstructorSuperExpression(ConstructorSuperExpression value);

  /**
   * Returns the value of the '<em><b>Constructor Field Expression</b></em>' containment reference list.
   * The list contents are of type {@link org.xtext.example.dJ.ConstructorFieldExpression}.
   * <!-- begin-user-doc -->
   * <p>
   * If the meaning of the '<em>Constructor Field Expression</em>' containment reference list isn't clear,
   * there really should be more of a description here...
   * </p>
   * <!-- end-user-doc -->
   * @return the value of the '<em>Constructor Field Expression</em>' containment reference list.
   * @see org.xtext.example.dJ.DJPackage#getConstructor_ConstructorFieldExpression()
   * @model containment="true"
   * @generated
   */
  EList<ConstructorFieldExpression> getConstructorFieldExpression();

} // Constructor
