/**
 * <copyright>
 * </copyright>
 *
 */
package org.xtext.example.dJ;

import org.eclipse.emf.ecore.EObject;

/**
 * <!-- begin-user-doc -->
 * A representation of the model object '<em><b>Modifies Class</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * <ul>
 *   <li>{@link org.xtext.example.dJ.ModifiesClass#getClass_ <em>Class</em>}</li>
 *   <li>{@link org.xtext.example.dJ.ModifiesClass#getExtends <em>Extends</em>}</li>
 *   <li>{@link org.xtext.example.dJ.ModifiesClass#getField <em>Field</em>}</li>
 *   <li>{@link org.xtext.example.dJ.ModifiesClass#getConstructor <em>Constructor</em>}</li>
 *   <li>{@link org.xtext.example.dJ.ModifiesClass#getMethod <em>Method</em>}</li>
 * </ul>
 * </p>
 *
 * @see org.xtext.example.dJ.DJPackage#getModifiesClass()
 * @model
 * @generated
 */
public interface ModifiesClass extends EObject
{
  /**
   * Returns the value of the '<em><b>Class</b></em>' reference.
   * <!-- begin-user-doc -->
   * <p>
   * If the meaning of the '<em>Class</em>' reference isn't clear,
   * there really should be more of a description here...
   * </p>
   * <!-- end-user-doc -->
   * @return the value of the '<em>Class</em>' reference.
   * @see #setClass(org.xtext.example.dJ.Class)
   * @see org.xtext.example.dJ.DJPackage#getModifiesClass_Class()
   * @model
   * @generated
   */
  org.xtext.example.dJ.Class getClass_();

  /**
   * Sets the value of the '{@link org.xtext.example.dJ.ModifiesClass#getClass_ <em>Class</em>}' reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @param value the new value of the '<em>Class</em>' reference.
   * @see #getClass_()
   * @generated
   */
  void setClass(org.xtext.example.dJ.Class value);

  /**
   * Returns the value of the '<em><b>Extends</b></em>' reference.
   * <!-- begin-user-doc -->
   * <p>
   * If the meaning of the '<em>Extends</em>' reference isn't clear,
   * there really should be more of a description here...
   * </p>
   * <!-- end-user-doc -->
   * @return the value of the '<em>Extends</em>' reference.
   * @see #setExtends(org.xtext.example.dJ.Class)
   * @see org.xtext.example.dJ.DJPackage#getModifiesClass_Extends()
   * @model
   * @generated
   */
  org.xtext.example.dJ.Class getExtends();

  /**
   * Sets the value of the '{@link org.xtext.example.dJ.ModifiesClass#getExtends <em>Extends</em>}' reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @param value the new value of the '<em>Extends</em>' reference.
   * @see #getExtends()
   * @generated
   */
  void setExtends(org.xtext.example.dJ.Class value);

  /**
   * Returns the value of the '<em><b>Field</b></em>' containment reference.
   * <!-- begin-user-doc -->
   * <p>
   * If the meaning of the '<em>Field</em>' containment reference isn't clear,
   * there really should be more of a description here...
   * </p>
   * <!-- end-user-doc -->
   * @return the value of the '<em>Field</em>' containment reference.
   * @see #setField(Fieldm)
   * @see org.xtext.example.dJ.DJPackage#getModifiesClass_Field()
   * @model containment="true"
   * @generated
   */
  Fieldm getField();

  /**
   * Sets the value of the '{@link org.xtext.example.dJ.ModifiesClass#getField <em>Field</em>}' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @param value the new value of the '<em>Field</em>' containment reference.
   * @see #getField()
   * @generated
   */
  void setField(Fieldm value);

  /**
   * Returns the value of the '<em><b>Constructor</b></em>' containment reference.
   * <!-- begin-user-doc -->
   * <p>
   * If the meaning of the '<em>Constructor</em>' containment reference isn't clear,
   * there really should be more of a description here...
   * </p>
   * <!-- end-user-doc -->
   * @return the value of the '<em>Constructor</em>' containment reference.
   * @see #setConstructor(Constructor)
   * @see org.xtext.example.dJ.DJPackage#getModifiesClass_Constructor()
   * @model containment="true"
   * @generated
   */
  Constructor getConstructor();

  /**
   * Sets the value of the '{@link org.xtext.example.dJ.ModifiesClass#getConstructor <em>Constructor</em>}' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @param value the new value of the '<em>Constructor</em>' containment reference.
   * @see #getConstructor()
   * @generated
   */
  void setConstructor(Constructor value);

  /**
   * Returns the value of the '<em><b>Method</b></em>' containment reference.
   * <!-- begin-user-doc -->
   * <p>
   * If the meaning of the '<em>Method</em>' containment reference isn't clear,
   * there really should be more of a description here...
   * </p>
   * <!-- end-user-doc -->
   * @return the value of the '<em>Method</em>' containment reference.
   * @see #setMethod(Methodm)
   * @see org.xtext.example.dJ.DJPackage#getModifiesClass_Method()
   * @model containment="true"
   * @generated
   */
  Methodm getMethod();

  /**
   * Sets the value of the '{@link org.xtext.example.dJ.ModifiesClass#getMethod <em>Method</em>}' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @param value the new value of the '<em>Method</em>' containment reference.
   * @see #getMethod()
   * @generated
   */
  void setMethod(Methodm value);

} // ModifiesClass
