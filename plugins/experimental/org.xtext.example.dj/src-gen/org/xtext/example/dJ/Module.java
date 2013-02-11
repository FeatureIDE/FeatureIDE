/**
 * <copyright>
 * </copyright>
 *
 */
package org.xtext.example.dJ;

import org.eclipse.emf.ecore.EObject;

/**
 * <!-- begin-user-doc -->
 * A representation of the model object '<em><b>Module</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * <ul>
 *   <li>{@link org.xtext.example.dJ.Module#getNtype <em>Ntype</em>}</li>
 *   <li>{@link org.xtext.example.dJ.Module#getCore <em>Core</em>}</li>
 *   <li>{@link org.xtext.example.dJ.Module#getDelta <em>Delta</em>}</li>
 * </ul>
 * </p>
 *
 * @see org.xtext.example.dJ.DJPackage#getModule()
 * @model
 * @generated
 */
public interface Module extends EObject
{
  /**
   * Returns the value of the '<em><b>Ntype</b></em>' attribute.
   * <!-- begin-user-doc -->
   * <p>
   * If the meaning of the '<em>Ntype</em>' attribute isn't clear,
   * there really should be more of a description here...
   * </p>
   * <!-- end-user-doc -->
   * @return the value of the '<em>Ntype</em>' attribute.
   * @see #setNtype(String)
   * @see org.xtext.example.dJ.DJPackage#getModule_Ntype()
   * @model
   * @generated
   */
  String getNtype();

  /**
   * Sets the value of the '{@link org.xtext.example.dJ.Module#getNtype <em>Ntype</em>}' attribute.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @param value the new value of the '<em>Ntype</em>' attribute.
   * @see #getNtype()
   * @generated
   */
  void setNtype(String value);

  /**
   * Returns the value of the '<em><b>Core</b></em>' containment reference.
   * <!-- begin-user-doc -->
   * <p>
   * If the meaning of the '<em>Core</em>' containment reference isn't clear,
   * there really should be more of a description here...
   * </p>
   * <!-- end-user-doc -->
   * @return the value of the '<em>Core</em>' containment reference.
   * @see #setCore(Core)
   * @see org.xtext.example.dJ.DJPackage#getModule_Core()
   * @model containment="true"
   * @generated
   */
  Core getCore();

  /**
   * Sets the value of the '{@link org.xtext.example.dJ.Module#getCore <em>Core</em>}' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @param value the new value of the '<em>Core</em>' containment reference.
   * @see #getCore()
   * @generated
   */
  void setCore(Core value);

  /**
   * Returns the value of the '<em><b>Delta</b></em>' containment reference.
   * <!-- begin-user-doc -->
   * <p>
   * If the meaning of the '<em>Delta</em>' containment reference isn't clear,
   * there really should be more of a description here...
   * </p>
   * <!-- end-user-doc -->
   * @return the value of the '<em>Delta</em>' containment reference.
   * @see #setDelta(Delta)
   * @see org.xtext.example.dJ.DJPackage#getModule_Delta()
   * @model containment="true"
   * @generated
   */
  Delta getDelta();

  /**
   * Sets the value of the '{@link org.xtext.example.dJ.Module#getDelta <em>Delta</em>}' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @param value the new value of the '<em>Delta</em>' containment reference.
   * @see #getDelta()
   * @generated
   */
  void setDelta(Delta value);

} // Module
