/**
 * <copyright>
 * </copyright>
 *
 */
package org.xtext.example.dJ;

import org.eclipse.emf.ecore.EObject;

/**
 * <!-- begin-user-doc -->
 * A representation of the model object '<em><b>Classm</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * <ul>
 *   <li>{@link org.xtext.example.dJ.Classm#getAction <em>Action</em>}</li>
 *   <li>{@link org.xtext.example.dJ.Classm#getModifies <em>Modifies</em>}</li>
 *   <li>{@link org.xtext.example.dJ.Classm#getAdds <em>Adds</em>}</li>
 *   <li>{@link org.xtext.example.dJ.Classm#getRemove <em>Remove</em>}</li>
 * </ul>
 * </p>
 *
 * @see org.xtext.example.dJ.DJPackage#getClassm()
 * @model
 * @generated
 */
public interface Classm extends EObject
{
  /**
   * Returns the value of the '<em><b>Action</b></em>' attribute.
   * <!-- begin-user-doc -->
   * <p>
   * If the meaning of the '<em>Action</em>' attribute isn't clear,
   * there really should be more of a description here...
   * </p>
   * <!-- end-user-doc -->
   * @return the value of the '<em>Action</em>' attribute.
   * @see #setAction(String)
   * @see org.xtext.example.dJ.DJPackage#getClassm_Action()
   * @model
   * @generated
   */
  String getAction();

  /**
   * Sets the value of the '{@link org.xtext.example.dJ.Classm#getAction <em>Action</em>}' attribute.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @param value the new value of the '<em>Action</em>' attribute.
   * @see #getAction()
   * @generated
   */
  void setAction(String value);

  /**
   * Returns the value of the '<em><b>Modifies</b></em>' containment reference.
   * <!-- begin-user-doc -->
   * <p>
   * If the meaning of the '<em>Modifies</em>' containment reference isn't clear,
   * there really should be more of a description here...
   * </p>
   * <!-- end-user-doc -->
   * @return the value of the '<em>Modifies</em>' containment reference.
   * @see #setModifies(ModifiesClass)
   * @see org.xtext.example.dJ.DJPackage#getClassm_Modifies()
   * @model containment="true"
   * @generated
   */
  ModifiesClass getModifies();

  /**
   * Sets the value of the '{@link org.xtext.example.dJ.Classm#getModifies <em>Modifies</em>}' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @param value the new value of the '<em>Modifies</em>' containment reference.
   * @see #getModifies()
   * @generated
   */
  void setModifies(ModifiesClass value);

  /**
   * Returns the value of the '<em><b>Adds</b></em>' containment reference.
   * <!-- begin-user-doc -->
   * <p>
   * If the meaning of the '<em>Adds</em>' containment reference isn't clear,
   * there really should be more of a description here...
   * </p>
   * <!-- end-user-doc -->
   * @return the value of the '<em>Adds</em>' containment reference.
   * @see #setAdds(AddsClass)
   * @see org.xtext.example.dJ.DJPackage#getClassm_Adds()
   * @model containment="true"
   * @generated
   */
  AddsClass getAdds();

  /**
   * Sets the value of the '{@link org.xtext.example.dJ.Classm#getAdds <em>Adds</em>}' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @param value the new value of the '<em>Adds</em>' containment reference.
   * @see #getAdds()
   * @generated
   */
  void setAdds(AddsClass value);

  /**
   * Returns the value of the '<em><b>Remove</b></em>' containment reference.
   * <!-- begin-user-doc -->
   * <p>
   * If the meaning of the '<em>Remove</em>' containment reference isn't clear,
   * there really should be more of a description here...
   * </p>
   * <!-- end-user-doc -->
   * @return the value of the '<em>Remove</em>' containment reference.
   * @see #setRemove(RemoveClass)
   * @see org.xtext.example.dJ.DJPackage#getClassm_Remove()
   * @model containment="true"
   * @generated
   */
  RemoveClass getRemove();

  /**
   * Sets the value of the '{@link org.xtext.example.dJ.Classm#getRemove <em>Remove</em>}' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @param value the new value of the '<em>Remove</em>' containment reference.
   * @see #getRemove()
   * @generated
   */
  void setRemove(RemoveClass value);

} // Classm
