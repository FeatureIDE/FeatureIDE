/**
 * <copyright>
 * </copyright>
 *
 */
package org.deltaj.deltaj;

import org.eclipse.emf.ecore.EObject;

/**
 * <!-- begin-user-doc -->
 * A representation of the model object '<em><b>Module Reference</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * <ul>
 *   <li>{@link org.deltaj.deltaj.ModuleReference#getDeltaModule <em>Delta Module</em>}</li>
 *   <li>{@link org.deltaj.deltaj.ModuleReference#getWhen <em>When</em>}</li>
 * </ul>
 * </p>
 *
 * @see org.deltaj.deltaj.DeltajPackage#getModuleReference()
 * @model
 * @generated
 */
public interface ModuleReference extends EObject
{
  /**
   * Returns the value of the '<em><b>Delta Module</b></em>' reference.
   * <!-- begin-user-doc -->
   * <p>
   * If the meaning of the '<em>Delta Module</em>' reference isn't clear,
   * there really should be more of a description here...
   * </p>
   * <!-- end-user-doc -->
   * @return the value of the '<em>Delta Module</em>' reference.
   * @see #setDeltaModule(DeltaModule)
   * @see org.deltaj.deltaj.DeltajPackage#getModuleReference_DeltaModule()
   * @model
   * @generated
   */
  DeltaModule getDeltaModule();

  /**
   * Sets the value of the '{@link org.deltaj.deltaj.ModuleReference#getDeltaModule <em>Delta Module</em>}' reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @param value the new value of the '<em>Delta Module</em>' reference.
   * @see #getDeltaModule()
   * @generated
   */
  void setDeltaModule(DeltaModule value);

  /**
   * Returns the value of the '<em><b>When</b></em>' containment reference.
   * <!-- begin-user-doc -->
   * <p>
   * If the meaning of the '<em>When</em>' containment reference isn't clear,
   * there really should be more of a description here...
   * </p>
   * <!-- end-user-doc -->
   * @return the value of the '<em>When</em>' containment reference.
   * @see #setWhen(PropositionalFormula)
   * @see org.deltaj.deltaj.DeltajPackage#getModuleReference_When()
   * @model containment="true"
   * @generated
   */
  PropositionalFormula getWhen();

  /**
   * Sets the value of the '{@link org.deltaj.deltaj.ModuleReference#getWhen <em>When</em>}' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @param value the new value of the '<em>When</em>' containment reference.
   * @see #getWhen()
   * @generated
   */
  void setWhen(PropositionalFormula value);

} // ModuleReference
