/**
 * <copyright>
 * </copyright>
 *
 */
package org.deltaj.deltaj;

import org.eclipse.emf.common.util.EList;

/**
 * <!-- begin-user-doc -->
 * A representation of the model object '<em><b>Class Modification</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * <ul>
 *   <li>{@link org.deltaj.deltaj.ClassModification#getExtends <em>Extends</em>}</li>
 *   <li>{@link org.deltaj.deltaj.ClassModification#getSubActions <em>Sub Actions</em>}</li>
 * </ul>
 * </p>
 *
 * @see org.deltaj.deltaj.DeltajPackage#getClassModification()
 * @model
 * @generated
 */
public interface ClassModification extends RemovesOrModifiesClass
{
  /**
   * Returns the value of the '<em><b>Extends</b></em>' attribute.
   * <!-- begin-user-doc -->
   * <p>
   * If the meaning of the '<em>Extends</em>' attribute isn't clear,
   * there really should be more of a description here...
   * </p>
   * <!-- end-user-doc -->
   * @return the value of the '<em>Extends</em>' attribute.
   * @see #setExtends(String)
   * @see org.deltaj.deltaj.DeltajPackage#getClassModification_Extends()
   * @model
   * @generated
   */
  String getExtends();

  /**
   * Sets the value of the '{@link org.deltaj.deltaj.ClassModification#getExtends <em>Extends</em>}' attribute.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @param value the new value of the '<em>Extends</em>' attribute.
   * @see #getExtends()
   * @generated
   */
  void setExtends(String value);

  /**
   * Returns the value of the '<em><b>Sub Actions</b></em>' containment reference list.
   * The list contents are of type {@link org.deltaj.deltaj.DeltaSubAction}.
   * <!-- begin-user-doc -->
   * <p>
   * If the meaning of the '<em>Sub Actions</em>' containment reference list isn't clear,
   * there really should be more of a description here...
   * </p>
   * <!-- end-user-doc -->
   * @return the value of the '<em>Sub Actions</em>' containment reference list.
   * @see org.deltaj.deltaj.DeltajPackage#getClassModification_SubActions()
   * @model containment="true"
   * @generated
   */
  EList<DeltaSubAction> getSubActions();

} // ClassModification
