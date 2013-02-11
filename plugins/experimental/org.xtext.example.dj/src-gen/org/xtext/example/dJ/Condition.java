/**
 * <copyright>
 * </copyright>
 *
 */
package org.xtext.example.dJ;

import org.eclipse.emf.ecore.EObject;

/**
 * <!-- begin-user-doc -->
 * A representation of the model object '<em><b>Condition</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * <ul>
 *   <li>{@link org.xtext.example.dJ.Condition#getComplement <em>Complement</em>}</li>
 *   <li>{@link org.xtext.example.dJ.Condition#getCondition1 <em>Condition1</em>}</li>
 *   <li>{@link org.xtext.example.dJ.Condition#getOperation <em>Operation</em>}</li>
 *   <li>{@link org.xtext.example.dJ.Condition#getCondition2 <em>Condition2</em>}</li>
 *   <li>{@link org.xtext.example.dJ.Condition#getFeature <em>Feature</em>}</li>
 * </ul>
 * </p>
 *
 * @see org.xtext.example.dJ.DJPackage#getCondition()
 * @model
 * @generated
 */
public interface Condition extends EObject
{
  /**
   * Returns the value of the '<em><b>Complement</b></em>' attribute.
   * <!-- begin-user-doc -->
   * <p>
   * If the meaning of the '<em>Complement</em>' attribute isn't clear,
   * there really should be more of a description here...
   * </p>
   * <!-- end-user-doc -->
   * @return the value of the '<em>Complement</em>' attribute.
   * @see #setComplement(String)
   * @see org.xtext.example.dJ.DJPackage#getCondition_Complement()
   * @model
   * @generated
   */
  String getComplement();

  /**
   * Sets the value of the '{@link org.xtext.example.dJ.Condition#getComplement <em>Complement</em>}' attribute.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @param value the new value of the '<em>Complement</em>' attribute.
   * @see #getComplement()
   * @generated
   */
  void setComplement(String value);

  /**
   * Returns the value of the '<em><b>Condition1</b></em>' containment reference.
   * <!-- begin-user-doc -->
   * <p>
   * If the meaning of the '<em>Condition1</em>' containment reference isn't clear,
   * there really should be more of a description here...
   * </p>
   * <!-- end-user-doc -->
   * @return the value of the '<em>Condition1</em>' containment reference.
   * @see #setCondition1(Condition)
   * @see org.xtext.example.dJ.DJPackage#getCondition_Condition1()
   * @model containment="true"
   * @generated
   */
  Condition getCondition1();

  /**
   * Sets the value of the '{@link org.xtext.example.dJ.Condition#getCondition1 <em>Condition1</em>}' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @param value the new value of the '<em>Condition1</em>' containment reference.
   * @see #getCondition1()
   * @generated
   */
  void setCondition1(Condition value);

  /**
   * Returns the value of the '<em><b>Operation</b></em>' attribute.
   * <!-- begin-user-doc -->
   * <p>
   * If the meaning of the '<em>Operation</em>' attribute isn't clear,
   * there really should be more of a description here...
   * </p>
   * <!-- end-user-doc -->
   * @return the value of the '<em>Operation</em>' attribute.
   * @see #setOperation(String)
   * @see org.xtext.example.dJ.DJPackage#getCondition_Operation()
   * @model
   * @generated
   */
  String getOperation();

  /**
   * Sets the value of the '{@link org.xtext.example.dJ.Condition#getOperation <em>Operation</em>}' attribute.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @param value the new value of the '<em>Operation</em>' attribute.
   * @see #getOperation()
   * @generated
   */
  void setOperation(String value);

  /**
   * Returns the value of the '<em><b>Condition2</b></em>' containment reference.
   * <!-- begin-user-doc -->
   * <p>
   * If the meaning of the '<em>Condition2</em>' containment reference isn't clear,
   * there really should be more of a description here...
   * </p>
   * <!-- end-user-doc -->
   * @return the value of the '<em>Condition2</em>' containment reference.
   * @see #setCondition2(Condition)
   * @see org.xtext.example.dJ.DJPackage#getCondition_Condition2()
   * @model containment="true"
   * @generated
   */
  Condition getCondition2();

  /**
   * Sets the value of the '{@link org.xtext.example.dJ.Condition#getCondition2 <em>Condition2</em>}' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @param value the new value of the '<em>Condition2</em>' containment reference.
   * @see #getCondition2()
   * @generated
   */
  void setCondition2(Condition value);

  /**
   * Returns the value of the '<em><b>Feature</b></em>' reference.
   * <!-- begin-user-doc -->
   * <p>
   * If the meaning of the '<em>Feature</em>' reference isn't clear,
   * there really should be more of a description here...
   * </p>
   * <!-- end-user-doc -->
   * @return the value of the '<em>Feature</em>' reference.
   * @see #setFeature(Feature)
   * @see org.xtext.example.dJ.DJPackage#getCondition_Feature()
   * @model
   * @generated
   */
  Feature getFeature();

  /**
   * Sets the value of the '{@link org.xtext.example.dJ.Condition#getFeature <em>Feature</em>}' reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @param value the new value of the '<em>Feature</em>' reference.
   * @see #getFeature()
   * @generated
   */
  void setFeature(Feature value);

} // Condition
