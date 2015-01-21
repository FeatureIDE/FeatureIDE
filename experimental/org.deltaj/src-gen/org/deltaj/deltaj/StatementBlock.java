/**
 * <copyright>
 * </copyright>
 *
 */
package org.deltaj.deltaj;

import org.eclipse.emf.common.util.EList;

import org.eclipse.emf.ecore.EObject;

/**
 * <!-- begin-user-doc -->
 * A representation of the model object '<em><b>Statement Block</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * <ul>
 *   <li>{@link org.deltaj.deltaj.StatementBlock#getLocalvariables <em>Localvariables</em>}</li>
 *   <li>{@link org.deltaj.deltaj.StatementBlock#getStatements <em>Statements</em>}</li>
 * </ul>
 * </p>
 *
 * @see org.deltaj.deltaj.DeltajPackage#getStatementBlock()
 * @model
 * @generated
 */
public interface StatementBlock extends EObject
{
  /**
   * Returns the value of the '<em><b>Localvariables</b></em>' containment reference list.
   * The list contents are of type {@link org.deltaj.deltaj.LocalVariableDeclaration}.
   * <!-- begin-user-doc -->
   * <p>
   * If the meaning of the '<em>Localvariables</em>' containment reference list isn't clear,
   * there really should be more of a description here...
   * </p>
   * <!-- end-user-doc -->
   * @return the value of the '<em>Localvariables</em>' containment reference list.
   * @see org.deltaj.deltaj.DeltajPackage#getStatementBlock_Localvariables()
   * @model containment="true"
   * @generated
   */
  EList<LocalVariableDeclaration> getLocalvariables();

  /**
   * Returns the value of the '<em><b>Statements</b></em>' containment reference list.
   * The list contents are of type {@link org.deltaj.deltaj.Statement}.
   * <!-- begin-user-doc -->
   * <p>
   * If the meaning of the '<em>Statements</em>' containment reference list isn't clear,
   * there really should be more of a description here...
   * </p>
   * <!-- end-user-doc -->
   * @return the value of the '<em>Statements</em>' containment reference list.
   * @see org.deltaj.deltaj.DeltajPackage#getStatementBlock_Statements()
   * @model containment="true"
   * @generated
   */
  EList<Statement> getStatements();

} // StatementBlock
