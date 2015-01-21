/**
 * <copyright>
 * </copyright>
 *
 */
package org.deltaj.deltaj;


/**
 * <!-- begin-user-doc -->
 * A representation of the model object '<em><b>If Statement</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * <ul>
 *   <li>{@link org.deltaj.deltaj.IfStatement#getExpression <em>Expression</em>}</li>
 *   <li>{@link org.deltaj.deltaj.IfStatement#getThenBlock <em>Then Block</em>}</li>
 *   <li>{@link org.deltaj.deltaj.IfStatement#getElseBlock <em>Else Block</em>}</li>
 * </ul>
 * </p>
 *
 * @see org.deltaj.deltaj.DeltajPackage#getIfStatement()
 * @model
 * @generated
 */
public interface IfStatement extends Statement
{
  /**
   * Returns the value of the '<em><b>Expression</b></em>' containment reference.
   * <!-- begin-user-doc -->
   * <p>
   * If the meaning of the '<em>Expression</em>' containment reference isn't clear,
   * there really should be more of a description here...
   * </p>
   * <!-- end-user-doc -->
   * @return the value of the '<em>Expression</em>' containment reference.
   * @see #setExpression(Expression)
   * @see org.deltaj.deltaj.DeltajPackage#getIfStatement_Expression()
   * @model containment="true"
   * @generated
   */
  Expression getExpression();

  /**
   * Sets the value of the '{@link org.deltaj.deltaj.IfStatement#getExpression <em>Expression</em>}' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @param value the new value of the '<em>Expression</em>' containment reference.
   * @see #getExpression()
   * @generated
   */
  void setExpression(Expression value);

  /**
   * Returns the value of the '<em><b>Then Block</b></em>' containment reference.
   * <!-- begin-user-doc -->
   * <p>
   * If the meaning of the '<em>Then Block</em>' containment reference isn't clear,
   * there really should be more of a description here...
   * </p>
   * <!-- end-user-doc -->
   * @return the value of the '<em>Then Block</em>' containment reference.
   * @see #setThenBlock(StatementBlock)
   * @see org.deltaj.deltaj.DeltajPackage#getIfStatement_ThenBlock()
   * @model containment="true"
   * @generated
   */
  StatementBlock getThenBlock();

  /**
   * Sets the value of the '{@link org.deltaj.deltaj.IfStatement#getThenBlock <em>Then Block</em>}' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @param value the new value of the '<em>Then Block</em>' containment reference.
   * @see #getThenBlock()
   * @generated
   */
  void setThenBlock(StatementBlock value);

  /**
   * Returns the value of the '<em><b>Else Block</b></em>' containment reference.
   * <!-- begin-user-doc -->
   * <p>
   * If the meaning of the '<em>Else Block</em>' containment reference isn't clear,
   * there really should be more of a description here...
   * </p>
   * <!-- end-user-doc -->
   * @return the value of the '<em>Else Block</em>' containment reference.
   * @see #setElseBlock(StatementBlock)
   * @see org.deltaj.deltaj.DeltajPackage#getIfStatement_ElseBlock()
   * @model containment="true"
   * @generated
   */
  StatementBlock getElseBlock();

  /**
   * Sets the value of the '{@link org.deltaj.deltaj.IfStatement#getElseBlock <em>Else Block</em>}' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @param value the new value of the '<em>Else Block</em>' containment reference.
   * @see #getElseBlock()
   * @generated
   */
  void setElseBlock(StatementBlock value);

} // IfStatement
