/**
 * <copyright>
 * </copyright>
 *
 */
package org.deltaj.deltaj;


/**
 * <!-- begin-user-doc -->
 * A representation of the model object '<em><b>Class Addition</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * <ul>
 *   <li>{@link org.deltaj.deltaj.ClassAddition#getClass_ <em>Class</em>}</li>
 * </ul>
 * </p>
 *
 * @see org.deltaj.deltaj.DeltajPackage#getClassAddition()
 * @model
 * @generated
 */
public interface ClassAddition extends DeltaAction
{
  /**
   * Returns the value of the '<em><b>Class</b></em>' containment reference.
   * <!-- begin-user-doc -->
   * <p>
   * If the meaning of the '<em>Class</em>' containment reference isn't clear,
   * there really should be more of a description here...
   * </p>
   * <!-- end-user-doc -->
   * @return the value of the '<em>Class</em>' containment reference.
   * @see #setClass(org.deltaj.deltaj.Class)
   * @see org.deltaj.deltaj.DeltajPackage#getClassAddition_Class()
   * @model containment="true"
   * @generated
   */
  org.deltaj.deltaj.Class getClass_();

  /**
   * Sets the value of the '{@link org.deltaj.deltaj.ClassAddition#getClass_ <em>Class</em>}' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @param value the new value of the '<em>Class</em>' containment reference.
   * @see #getClass_()
   * @generated
   */
  void setClass(org.deltaj.deltaj.Class value);

} // ClassAddition
