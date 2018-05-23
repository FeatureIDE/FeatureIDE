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
 * A representation of the model object '<em><b>Partition Part</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * <ul>
 *   <li>{@link org.deltaj.deltaj.PartitionPart#getModuleReferences <em>Module References</em>}</li>
 * </ul>
 * </p>
 *
 * @see org.deltaj.deltaj.DeltajPackage#getPartitionPart()
 * @model
 * @generated
 */
public interface PartitionPart extends EObject
{
  /**
   * Returns the value of the '<em><b>Module References</b></em>' containment reference list.
   * The list contents are of type {@link org.deltaj.deltaj.ModuleReference}.
   * <!-- begin-user-doc -->
   * <p>
   * If the meaning of the '<em>Module References</em>' containment reference list isn't clear,
   * there really should be more of a description here...
   * </p>
   * <!-- end-user-doc -->
   * @return the value of the '<em>Module References</em>' containment reference list.
   * @see org.deltaj.deltaj.DeltajPackage#getPartitionPart_ModuleReferences()
   * @model containment="true"
   * @generated
   */
  EList<ModuleReference> getModuleReferences();

} // PartitionPart
