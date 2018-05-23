/**
 * <copyright>
 * </copyright>
 *
 */
package org.deltaj.deltaj;


/**
 * <!-- begin-user-doc -->
 * A representation of the model object '<em><b>Variable Access</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * <ul>
 *   <li>{@link org.deltaj.deltaj.VariableAccess#getVariable <em>Variable</em>}</li>
 * </ul>
 * </p>
 *
 * @see org.deltaj.deltaj.DeltajPackage#getVariableAccess()
 * @model
 * @generated
 */
public interface VariableAccess extends Expression
{
  /**
   * Returns the value of the '<em><b>Variable</b></em>' reference.
   * <!-- begin-user-doc -->
   * <p>
   * If the meaning of the '<em>Variable</em>' reference isn't clear,
   * there really should be more of a description here...
   * </p>
   * <!-- end-user-doc -->
   * @return the value of the '<em>Variable</em>' reference.
   * @see #setVariable(TypedDeclaration)
   * @see org.deltaj.deltaj.DeltajPackage#getVariableAccess_Variable()
   * @model
   * @generated
   */
  TypedDeclaration getVariable();

  /**
   * Sets the value of the '{@link org.deltaj.deltaj.VariableAccess#getVariable <em>Variable</em>}' reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @param value the new value of the '<em>Variable</em>' reference.
   * @see #getVariable()
   * @generated
   */
  void setVariable(TypedDeclaration value);

} // VariableAccess
