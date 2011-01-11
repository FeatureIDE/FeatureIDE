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
 * A representation of the model object '<em><b>Method Body</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * <ul>
 *   <li>{@link org.xtext.example.dJ.MethodBody#getInsertJava <em>Insert Java</em>}</li>
 *   <li>{@link org.xtext.example.dJ.MethodBody#getExpressions <em>Expressions</em>}</li>
 *   <li>{@link org.xtext.example.dJ.MethodBody#getReturn <em>Return</em>}</li>
 *   <li>{@link org.xtext.example.dJ.MethodBody#getExpressionReturn <em>Expression Return</em>}</li>
 * </ul>
 * </p>
 *
 * @see org.xtext.example.dJ.DJPackage#getMethodBody()
 * @model
 * @generated
 */
public interface MethodBody extends EObject
{
  /**
   * Returns the value of the '<em><b>Insert Java</b></em>' containment reference list.
   * The list contents are of type {@link org.xtext.example.dJ.InsertJava}.
   * <!-- begin-user-doc -->
   * <p>
   * If the meaning of the '<em>Insert Java</em>' containment reference list isn't clear,
   * there really should be more of a description here...
   * </p>
   * <!-- end-user-doc -->
   * @return the value of the '<em>Insert Java</em>' containment reference list.
   * @see org.xtext.example.dJ.DJPackage#getMethodBody_InsertJava()
   * @model containment="true"
   * @generated
   */
  EList<InsertJava> getInsertJava();

  /**
   * Returns the value of the '<em><b>Expressions</b></em>' containment reference list.
   * The list contents are of type {@link org.xtext.example.dJ.Expression}.
   * <!-- begin-user-doc -->
   * <p>
   * If the meaning of the '<em>Expressions</em>' containment reference list isn't clear,
   * there really should be more of a description here...
   * </p>
   * <!-- end-user-doc -->
   * @return the value of the '<em>Expressions</em>' containment reference list.
   * @see org.xtext.example.dJ.DJPackage#getMethodBody_Expressions()
   * @model containment="true"
   * @generated
   */
  EList<Expression> getExpressions();

  /**
   * Returns the value of the '<em><b>Return</b></em>' attribute.
   * <!-- begin-user-doc -->
   * <p>
   * If the meaning of the '<em>Return</em>' attribute isn't clear,
   * there really should be more of a description here...
   * </p>
   * <!-- end-user-doc -->
   * @return the value of the '<em>Return</em>' attribute.
   * @see #setReturn(String)
   * @see org.xtext.example.dJ.DJPackage#getMethodBody_Return()
   * @model
   * @generated
   */
  String getReturn();

  /**
   * Sets the value of the '{@link org.xtext.example.dJ.MethodBody#getReturn <em>Return</em>}' attribute.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @param value the new value of the '<em>Return</em>' attribute.
   * @see #getReturn()
   * @generated
   */
  void setReturn(String value);

  /**
   * Returns the value of the '<em><b>Expression Return</b></em>' containment reference.
   * <!-- begin-user-doc -->
   * <p>
   * If the meaning of the '<em>Expression Return</em>' containment reference isn't clear,
   * there really should be more of a description here...
   * </p>
   * <!-- end-user-doc -->
   * @return the value of the '<em>Expression Return</em>' containment reference.
   * @see #setExpressionReturn(Expression)
   * @see org.xtext.example.dJ.DJPackage#getMethodBody_ExpressionReturn()
   * @model containment="true"
   * @generated
   */
  Expression getExpressionReturn();

  /**
   * Sets the value of the '{@link org.xtext.example.dJ.MethodBody#getExpressionReturn <em>Expression Return</em>}' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @param value the new value of the '<em>Expression Return</em>' containment reference.
   * @see #getExpressionReturn()
   * @generated
   */
  void setExpressionReturn(Expression value);

} // MethodBody
