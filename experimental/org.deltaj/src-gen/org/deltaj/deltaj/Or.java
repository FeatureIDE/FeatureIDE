/**
 * <copyright>
 * </copyright>
 *
 */
package org.deltaj.deltaj;


/**
 * <!-- begin-user-doc -->
 * A representation of the model object '<em><b>Or</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * <ul>
 *   <li>{@link org.deltaj.deltaj.Or#getLeft <em>Left</em>}</li>
 *   <li>{@link org.deltaj.deltaj.Or#getRight <em>Right</em>}</li>
 * </ul>
 * </p>
 *
 * @see org.deltaj.deltaj.DeltajPackage#getOr()
 * @model
 * @generated
 */
public interface Or extends PropositionalFormula
{
  /**
   * Returns the value of the '<em><b>Left</b></em>' containment reference.
   * <!-- begin-user-doc -->
   * <p>
   * If the meaning of the '<em>Left</em>' containment reference isn't clear,
   * there really should be more of a description here...
   * </p>
   * <!-- end-user-doc -->
   * @return the value of the '<em>Left</em>' containment reference.
   * @see #setLeft(PropositionalFormula)
   * @see org.deltaj.deltaj.DeltajPackage#getOr_Left()
   * @model containment="true"
   * @generated
   */
  PropositionalFormula getLeft();

  /**
   * Sets the value of the '{@link org.deltaj.deltaj.Or#getLeft <em>Left</em>}' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @param value the new value of the '<em>Left</em>' containment reference.
   * @see #getLeft()
   * @generated
   */
  void setLeft(PropositionalFormula value);

  /**
   * Returns the value of the '<em><b>Right</b></em>' containment reference.
   * <!-- begin-user-doc -->
   * <p>
   * If the meaning of the '<em>Right</em>' containment reference isn't clear,
   * there really should be more of a description here...
   * </p>
   * <!-- end-user-doc -->
   * @return the value of the '<em>Right</em>' containment reference.
   * @see #setRight(PropositionalFormula)
   * @see org.deltaj.deltaj.DeltajPackage#getOr_Right()
   * @model containment="true"
   * @generated
   */
  PropositionalFormula getRight();

  /**
   * Sets the value of the '{@link org.deltaj.deltaj.Or#getRight <em>Right</em>}' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @param value the new value of the '<em>Right</em>' containment reference.
   * @see #getRight()
   * @generated
   */
  void setRight(PropositionalFormula value);

} // Or
