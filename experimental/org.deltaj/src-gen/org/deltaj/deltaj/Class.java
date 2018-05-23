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
 * A representation of the model object '<em><b>Class</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * <ul>
 *   <li>{@link org.deltaj.deltaj.Class#getName <em>Name</em>}</li>
 *   <li>{@link org.deltaj.deltaj.Class#getExtends <em>Extends</em>}</li>
 *   <li>{@link org.deltaj.deltaj.Class#getFields <em>Fields</em>}</li>
 *   <li>{@link org.deltaj.deltaj.Class#getMethods <em>Methods</em>}</li>
 * </ul>
 * </p>
 *
 * @see org.deltaj.deltaj.DeltajPackage#getClass_()
 * @model
 * @generated
 */
public interface Class extends EObject
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
   * @see org.deltaj.deltaj.DeltajPackage#getClass_Name()
   * @model
   * @generated
   */
  String getName();

  /**
   * Sets the value of the '{@link org.deltaj.deltaj.Class#getName <em>Name</em>}' attribute.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @param value the new value of the '<em>Name</em>' attribute.
   * @see #getName()
   * @generated
   */
  void setName(String value);

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
   * @see org.deltaj.deltaj.DeltajPackage#getClass_Extends()
   * @model
   * @generated
   */
  String getExtends();

  /**
   * Sets the value of the '{@link org.deltaj.deltaj.Class#getExtends <em>Extends</em>}' attribute.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @param value the new value of the '<em>Extends</em>' attribute.
   * @see #getExtends()
   * @generated
   */
  void setExtends(String value);

  /**
   * Returns the value of the '<em><b>Fields</b></em>' containment reference list.
   * The list contents are of type {@link org.deltaj.deltaj.Field}.
   * <!-- begin-user-doc -->
   * <p>
   * If the meaning of the '<em>Fields</em>' containment reference list isn't clear,
   * there really should be more of a description here...
   * </p>
   * <!-- end-user-doc -->
   * @return the value of the '<em>Fields</em>' containment reference list.
   * @see org.deltaj.deltaj.DeltajPackage#getClass_Fields()
   * @model containment="true"
   * @generated
   */
  EList<Field> getFields();

  /**
   * Returns the value of the '<em><b>Methods</b></em>' containment reference list.
   * The list contents are of type {@link org.deltaj.deltaj.Method}.
   * <!-- begin-user-doc -->
   * <p>
   * If the meaning of the '<em>Methods</em>' containment reference list isn't clear,
   * there really should be more of a description here...
   * </p>
   * <!-- end-user-doc -->
   * @return the value of the '<em>Methods</em>' containment reference list.
   * @see org.deltaj.deltaj.DeltajPackage#getClass_Methods()
   * @model containment="true"
   * @generated
   */
  EList<Method> getMethods();

} // Class
