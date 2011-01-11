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
 * A representation of the model object '<em><b>Constructor Super Expression</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * <ul>
 *   <li>{@link org.xtext.example.dJ.ConstructorSuperExpression#getParS <em>Par S</em>}</li>
 * </ul>
 * </p>
 *
 * @see org.xtext.example.dJ.DJPackage#getConstructorSuperExpression()
 * @model
 * @generated
 */
public interface ConstructorSuperExpression extends EObject
{
  /**
   * Returns the value of the '<em><b>Par S</b></em>' reference list.
   * The list contents are of type {@link org.xtext.example.dJ.Parameter}.
   * <!-- begin-user-doc -->
   * <p>
   * If the meaning of the '<em>Par S</em>' reference list isn't clear,
   * there really should be more of a description here...
   * </p>
   * <!-- end-user-doc -->
   * @return the value of the '<em>Par S</em>' reference list.
   * @see org.xtext.example.dJ.DJPackage#getConstructorSuperExpression_ParS()
   * @model
   * @generated
   */
  EList<Parameter> getParS();

} // ConstructorSuperExpression
