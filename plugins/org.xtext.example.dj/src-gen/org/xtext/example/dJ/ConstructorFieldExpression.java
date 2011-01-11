/**
 * <copyright>
 * </copyright>
 *
 */
package org.xtext.example.dJ;

import org.eclipse.emf.ecore.EObject;

/**
 * <!-- begin-user-doc -->
 * A representation of the model object '<em><b>Constructor Field Expression</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * <ul>
 *   <li>{@link org.xtext.example.dJ.ConstructorFieldExpression#getField <em>Field</em>}</li>
 *   <li>{@link org.xtext.example.dJ.ConstructorFieldExpression#getParT <em>Par T</em>}</li>
 * </ul>
 * </p>
 *
 * @see org.xtext.example.dJ.DJPackage#getConstructorFieldExpression()
 * @model
 * @generated
 */
public interface ConstructorFieldExpression extends EObject
{
  /**
   * Returns the value of the '<em><b>Field</b></em>' reference.
   * <!-- begin-user-doc -->
   * <p>
   * If the meaning of the '<em>Field</em>' reference isn't clear,
   * there really should be more of a description here...
   * </p>
   * <!-- end-user-doc -->
   * @return the value of the '<em>Field</em>' reference.
   * @see #setField(FieldRef)
   * @see org.xtext.example.dJ.DJPackage#getConstructorFieldExpression_Field()
   * @model
   * @generated
   */
  FieldRef getField();

  /**
   * Sets the value of the '{@link org.xtext.example.dJ.ConstructorFieldExpression#getField <em>Field</em>}' reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @param value the new value of the '<em>Field</em>' reference.
   * @see #getField()
   * @generated
   */
  void setField(FieldRef value);

  /**
   * Returns the value of the '<em><b>Par T</b></em>' reference.
   * <!-- begin-user-doc -->
   * <p>
   * If the meaning of the '<em>Par T</em>' reference isn't clear,
   * there really should be more of a description here...
   * </p>
   * <!-- end-user-doc -->
   * @return the value of the '<em>Par T</em>' reference.
   * @see #setParT(Parameter)
   * @see org.xtext.example.dJ.DJPackage#getConstructorFieldExpression_ParT()
   * @model
   * @generated
   */
  Parameter getParT();

  /**
   * Sets the value of the '{@link org.xtext.example.dJ.ConstructorFieldExpression#getParT <em>Par T</em>}' reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @param value the new value of the '<em>Par T</em>' reference.
   * @see #getParT()
   * @generated
   */
  void setParT(Parameter value);

} // ConstructorFieldExpression
