/**
 * <copyright>
 * </copyright>
 *
 */
package org.deltaj.deltaj;


/**
 * <!-- begin-user-doc -->
 * A representation of the model object '<em><b>Class Type</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * <ul>
 *   <li>{@link org.deltaj.deltaj.ClassType#getClassref <em>Classref</em>}</li>
 * </ul>
 * </p>
 *
 * @see org.deltaj.deltaj.DeltajPackage#getClassType()
 * @model
 * @generated
 */
public interface ClassType extends TypeForDeclaration
{
  /**
   * Returns the value of the '<em><b>Classref</b></em>' attribute.
   * <!-- begin-user-doc -->
   * <p>
   * If the meaning of the '<em>Classref</em>' attribute isn't clear,
   * there really should be more of a description here...
   * </p>
   * <!-- end-user-doc -->
   * @return the value of the '<em>Classref</em>' attribute.
   * @see #setClassref(String)
   * @see org.deltaj.deltaj.DeltajPackage#getClassType_Classref()
   * @model
   * @generated
   */
  String getClassref();

  /**
   * Sets the value of the '{@link org.deltaj.deltaj.ClassType#getClassref <em>Classref</em>}' attribute.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @param value the new value of the '<em>Classref</em>' attribute.
   * @see #getClassref()
   * @generated
   */
  void setClassref(String value);

} // ClassType
