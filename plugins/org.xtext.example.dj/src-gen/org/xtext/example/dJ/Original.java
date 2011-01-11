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
 * A representation of the model object '<em><b>Original</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * <ul>
 *   <li>{@link org.xtext.example.dJ.Original#getPar <em>Par</em>}</li>
 * </ul>
 * </p>
 *
 * @see org.xtext.example.dJ.DJPackage#getOriginal()
 * @model
 * @generated
 */
public interface Original extends EObject
{
  /**
   * Returns the value of the '<em><b>Par</b></em>' reference list.
   * The list contents are of type {@link org.xtext.example.dJ.Parameter}.
   * <!-- begin-user-doc -->
   * <p>
   * If the meaning of the '<em>Par</em>' reference list isn't clear,
   * there really should be more of a description here...
   * </p>
   * <!-- end-user-doc -->
   * @return the value of the '<em>Par</em>' reference list.
   * @see org.xtext.example.dJ.DJPackage#getOriginal_Par()
   * @model
   * @generated
   */
  EList<Parameter> getPar();

} // Original
