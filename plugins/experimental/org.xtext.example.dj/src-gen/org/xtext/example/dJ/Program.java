/**
 * <copyright>
 * </copyright>
 *
 */
package org.xtext.example.dJ;

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
 *   <li>{@link org.xtext.example.dJ.Program#getImports <em>Imports</em>}</li>
 *   <li>{@link org.xtext.example.dJ.Program#getFeatures <em>Features</em>}</li>
 *   <li>{@link org.xtext.example.dJ.Program#getModulesList <em>Modules List</em>}</li>
 * </ul>
 * </p>
 *
 * @see org.xtext.example.dJ.DJPackage#getProgram()
 * @model
 * @generated
 */
public interface Program extends EObject
{
  /**
   * Returns the value of the '<em><b>Imports</b></em>' containment reference list.
   * The list contents are of type {@link org.xtext.example.dJ.Import}.
   * <!-- begin-user-doc -->
   * <p>
   * If the meaning of the '<em>Imports</em>' containment reference list isn't clear,
   * there really should be more of a description here...
   * </p>
   * <!-- end-user-doc -->
   * @return the value of the '<em>Imports</em>' containment reference list.
   * @see org.xtext.example.dJ.DJPackage#getProgram_Imports()
   * @model containment="true"
   * @generated
   */
  EList<Import> getImports();

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
   * @see org.xtext.example.dJ.DJPackage#getProgram_Features()
   * @model containment="true"
   * @generated
   */
  Features getFeatures();

  /**
   * Sets the value of the '{@link org.xtext.example.dJ.Program#getFeatures <em>Features</em>}' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @param value the new value of the '<em>Features</em>' containment reference.
   * @see #getFeatures()
   * @generated
   */
  void setFeatures(Features value);

  /**
   * Returns the value of the '<em><b>Modules List</b></em>' containment reference list.
   * The list contents are of type {@link org.xtext.example.dJ.Module}.
   * <!-- begin-user-doc -->
   * <p>
   * If the meaning of the '<em>Modules List</em>' containment reference list isn't clear,
   * there really should be more of a description here...
   * </p>
   * <!-- end-user-doc -->
   * @return the value of the '<em>Modules List</em>' containment reference list.
   * @see org.xtext.example.dJ.DJPackage#getProgram_ModulesList()
   * @model containment="true"
   * @generated
   */
  EList<Module> getModulesList();

} // Program
