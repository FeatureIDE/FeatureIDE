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
 * A representation of the model object '<em><b>Product</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * <ul>
 *   <li>{@link org.deltaj.deltaj.Product#getName <em>Name</em>}</li>
 *   <li>{@link org.deltaj.deltaj.Product#getProductLine <em>Product Line</em>}</li>
 *   <li>{@link org.deltaj.deltaj.Product#getFeatures <em>Features</em>}</li>
 * </ul>
 * </p>
 *
 * @see org.deltaj.deltaj.DeltajPackage#getProduct()
 * @model
 * @generated
 */
public interface Product extends EObject
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
   * @see org.deltaj.deltaj.DeltajPackage#getProduct_Name()
   * @model
   * @generated
   */
  String getName();

  /**
   * Sets the value of the '{@link org.deltaj.deltaj.Product#getName <em>Name</em>}' attribute.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @param value the new value of the '<em>Name</em>' attribute.
   * @see #getName()
   * @generated
   */
  void setName(String value);

  /**
   * Returns the value of the '<em><b>Product Line</b></em>' reference.
   * <!-- begin-user-doc -->
   * <p>
   * If the meaning of the '<em>Product Line</em>' reference isn't clear,
   * there really should be more of a description here...
   * </p>
   * <!-- end-user-doc -->
   * @return the value of the '<em>Product Line</em>' reference.
   * @see #setProductLine(ProductLine)
   * @see org.deltaj.deltaj.DeltajPackage#getProduct_ProductLine()
   * @model
   * @generated
   */
  ProductLine getProductLine();

  /**
   * Sets the value of the '{@link org.deltaj.deltaj.Product#getProductLine <em>Product Line</em>}' reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @param value the new value of the '<em>Product Line</em>' reference.
   * @see #getProductLine()
   * @generated
   */
  void setProductLine(ProductLine value);

  /**
   * Returns the value of the '<em><b>Features</b></em>' reference list.
   * The list contents are of type {@link org.deltaj.deltaj.Feature}.
   * <!-- begin-user-doc -->
   * <p>
   * If the meaning of the '<em>Features</em>' reference list isn't clear,
   * there really should be more of a description here...
   * </p>
   * <!-- end-user-doc -->
   * @return the value of the '<em>Features</em>' reference list.
   * @see org.deltaj.deltaj.DeltajPackage#getProduct_Features()
   * @model
   * @generated
   */
  EList<Feature> getFeatures();

} // Product
