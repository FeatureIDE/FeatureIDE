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
 * A representation of the model object '<em><b>Delta Module</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * <ul>
 *   <li>{@link org.deltaj.deltaj.DeltaModule#getName <em>Name</em>}</li>
 *   <li>{@link org.deltaj.deltaj.DeltaModule#getDeltaActions <em>Delta Actions</em>}</li>
 * </ul>
 * </p>
 *
 * @see org.deltaj.deltaj.DeltajPackage#getDeltaModule()
 * @model
 * @generated
 */
public interface DeltaModule extends EObject
{
  /**
   * Returns the value of the '<em><b>Name</b></em>' attribute.
   * <!-- begin-user-doc -->
   * <p>
   * If the meaning of the '<em>Name</em>' attribute isn't clear,
   * there really should be more of a description here...
   * </p>
   * <!-- end-user-doc -->
   * @return the value of the '<em>Name</em>' attribute.
   * @see #setName(String)
   * @see org.deltaj.deltaj.DeltajPackage#getDeltaModule_Name()
   * @model
   * @generated
   */
  String getName();

  /**
   * Sets the value of the '{@link org.deltaj.deltaj.DeltaModule#getName <em>Name</em>}' attribute.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @param value the new value of the '<em>Name</em>' attribute.
   * @see #getName()
   * @generated
   */
  void setName(String value);

  /**
   * Returns the value of the '<em><b>Delta Actions</b></em>' containment reference list.
   * The list contents are of type {@link org.deltaj.deltaj.DeltaAction}.
   * <!-- begin-user-doc -->
   * <p>
   * If the meaning of the '<em>Delta Actions</em>' containment reference list isn't clear,
   * there really should be more of a description here...
   * </p>
   * <!-- end-user-doc -->
   * @return the value of the '<em>Delta Actions</em>' containment reference list.
   * @see org.deltaj.deltaj.DeltajPackage#getDeltaModule_DeltaActions()
   * @model containment="true"
   * @generated
   */
  EList<DeltaAction> getDeltaActions();

} // DeltaModule
