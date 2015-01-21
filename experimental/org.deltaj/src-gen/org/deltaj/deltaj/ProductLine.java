/**
 * <copyright>
 * </copyright>
 *
 */
package org.deltaj.deltaj;

import org.eclipse.emf.ecore.EObject;

/**
 * <!-- begin-user-doc -->
 * A representation of the model object '<em><b>Product Line</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * <ul>
 *   <li>{@link org.deltaj.deltaj.ProductLine#getName <em>Name</em>}</li>
 *   <li>{@link org.deltaj.deltaj.ProductLine#getFeatures <em>Features</em>}</li>
 *   <li>{@link org.deltaj.deltaj.ProductLine#getConfigurations <em>Configurations</em>}</li>
 *   <li>{@link org.deltaj.deltaj.ProductLine#getPartition <em>Partition</em>}</li>
 * </ul>
 * </p>
 *
 * @see org.deltaj.deltaj.DeltajPackage#getProductLine()
 * @model
 * @generated
 */
public interface ProductLine extends EObject
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
   * @see org.deltaj.deltaj.DeltajPackage#getProductLine_Name()
   * @model
   * @generated
   */
  String getName();

  /**
   * Sets the value of the '{@link org.deltaj.deltaj.ProductLine#getName <em>Name</em>}' attribute.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @param value the new value of the '<em>Name</em>' attribute.
   * @see #getName()
   * @generated
   */
  void setName(String value);

  /**
   * Returns the value of the '<em><b>Features</b></em>' containment reference.
   * <!-- begin-user-doc -->
   * <p>
   * If the meaning of the '<em>Features</em>' containment reference isn't clear,
   * there really should be more of a description here...
   * </p>
   * <!-- end-user-doc -->
   * @return the value of the '<em>Features</em>' containment reference.
   * @see #setFeatures(Features)
   * @see org.deltaj.deltaj.DeltajPackage#getProductLine_Features()
   * @model containment="true"
   * @generated
   */
  Features getFeatures();

  /**
   * Sets the value of the '{@link org.deltaj.deltaj.ProductLine#getFeatures <em>Features</em>}' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @param value the new value of the '<em>Features</em>' containment reference.
   * @see #getFeatures()
   * @generated
   */
  void setFeatures(Features value);

  /**
   * Returns the value of the '<em><b>Configurations</b></em>' containment reference.
   * <!-- begin-user-doc -->
   * <p>
   * If the meaning of the '<em>Configurations</em>' containment reference isn't clear,
   * there really should be more of a description here...
   * </p>
   * <!-- end-user-doc -->
   * @return the value of the '<em>Configurations</em>' containment reference.
   * @see #setConfigurations(Configurations)
   * @see org.deltaj.deltaj.DeltajPackage#getProductLine_Configurations()
   * @model containment="true"
   * @generated
   */
  Configurations getConfigurations();

  /**
   * Sets the value of the '{@link org.deltaj.deltaj.ProductLine#getConfigurations <em>Configurations</em>}' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @param value the new value of the '<em>Configurations</em>' containment reference.
   * @see #getConfigurations()
   * @generated
   */
  void setConfigurations(Configurations value);

  /**
   * Returns the value of the '<em><b>Partition</b></em>' containment reference.
   * <!-- begin-user-doc -->
   * <p>
   * If the meaning of the '<em>Partition</em>' containment reference isn't clear,
   * there really should be more of a description here...
   * </p>
   * <!-- end-user-doc -->
   * @return the value of the '<em>Partition</em>' containment reference.
   * @see #setPartition(DeltaPartition)
   * @see org.deltaj.deltaj.DeltajPackage#getProductLine_Partition()
   * @model containment="true"
   * @generated
   */
  DeltaPartition getPartition();

  /**
   * Sets the value of the '{@link org.deltaj.deltaj.ProductLine#getPartition <em>Partition</em>}' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @param value the new value of the '<em>Partition</em>' containment reference.
   * @see #getPartition()
   * @generated
   */
  void setPartition(DeltaPartition value);

} // ProductLine
