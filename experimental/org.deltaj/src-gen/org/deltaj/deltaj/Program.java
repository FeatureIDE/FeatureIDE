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
 * A representation of the model object '<em><b>Program</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * <ul>
 *   <li>{@link org.deltaj.deltaj.Program#getDeltaModules <em>Delta Modules</em>}</li>
 *   <li>{@link org.deltaj.deltaj.Program#getProductLines <em>Product Lines</em>}</li>
 *   <li>{@link org.deltaj.deltaj.Program#getProducts <em>Products</em>}</li>
 * </ul>
 * </p>
 *
 * @see org.deltaj.deltaj.DeltajPackage#getProgram()
 * @model
 * @generated
 */
public interface Program extends EObject
{
  /**
   * Returns the value of the '<em><b>Delta Modules</b></em>' containment reference list.
   * The list contents are of type {@link org.deltaj.deltaj.DeltaModule}.
   * <!-- begin-user-doc -->
   * <p>
   * If the meaning of the '<em>Delta Modules</em>' containment reference list isn't clear,
   * there really should be more of a description here...
   * </p>
   * <!-- end-user-doc -->
   * @return the value of the '<em>Delta Modules</em>' containment reference list.
   * @see org.deltaj.deltaj.DeltajPackage#getProgram_DeltaModules()
   * @model containment="true"
   * @generated
   */
  EList<DeltaModule> getDeltaModules();

  /**
   * Returns the value of the '<em><b>Product Lines</b></em>' containment reference list.
   * The list contents are of type {@link org.deltaj.deltaj.ProductLine}.
   * <!-- begin-user-doc -->
   * <p>
   * If the meaning of the '<em>Product Lines</em>' containment reference list isn't clear,
   * there really should be more of a description here...
   * </p>
   * <!-- end-user-doc -->
   * @return the value of the '<em>Product Lines</em>' containment reference list.
   * @see org.deltaj.deltaj.DeltajPackage#getProgram_ProductLines()
   * @model containment="true"
   * @generated
   */
  EList<ProductLine> getProductLines();

  /**
   * Returns the value of the '<em><b>Products</b></em>' containment reference list.
   * The list contents are of type {@link org.deltaj.deltaj.Product}.
   * <!-- begin-user-doc -->
   * <p>
   * If the meaning of the '<em>Products</em>' containment reference list isn't clear,
   * there really should be more of a description here...
   * </p>
   * <!-- end-user-doc -->
   * @return the value of the '<em>Products</em>' containment reference list.
   * @see org.deltaj.deltaj.DeltajPackage#getProgram_Products()
   * @model containment="true"
   * @generated
   */
  EList<Product> getProducts();

} // Program
