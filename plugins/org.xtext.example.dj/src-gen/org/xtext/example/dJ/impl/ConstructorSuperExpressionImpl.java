/**
 * <copyright>
 * </copyright>
 *
 */
package org.xtext.example.dJ.impl;

import java.util.Collection;

import org.eclipse.emf.common.util.EList;

import org.eclipse.emf.ecore.EClass;

import org.eclipse.emf.ecore.impl.MinimalEObjectImpl;

import org.eclipse.emf.ecore.util.EObjectResolvingEList;

import org.xtext.example.dJ.ConstructorSuperExpression;
import org.xtext.example.dJ.DJPackage;
import org.xtext.example.dJ.Parameter;

/**
 * <!-- begin-user-doc -->
 * An implementation of the model object '<em><b>Constructor Super Expression</b></em>'.
 * <!-- end-user-doc -->
 * <p>
 * The following features are implemented:
 * <ul>
 *   <li>{@link org.xtext.example.dJ.impl.ConstructorSuperExpressionImpl#getParS <em>Par S</em>}</li>
 * </ul>
 * </p>
 *
 * @generated
 */
public class ConstructorSuperExpressionImpl extends MinimalEObjectImpl.Container implements ConstructorSuperExpression
{
  /**
   * The cached value of the '{@link #getParS() <em>Par S</em>}' reference list.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see #getParS()
   * @generated
   * @ordered
   */
  protected EList<Parameter> parS;

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  protected ConstructorSuperExpressionImpl()
  {
    super();
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  @Override
  protected EClass eStaticClass()
  {
    return DJPackage.Literals.CONSTRUCTOR_SUPER_EXPRESSION;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public EList<Parameter> getParS()
  {
    if (parS == null)
    {
      parS = new EObjectResolvingEList<Parameter>(Parameter.class, this, DJPackage.CONSTRUCTOR_SUPER_EXPRESSION__PAR_S);
    }
    return parS;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  @Override
  public Object eGet(int featureID, boolean resolve, boolean coreType)
  {
    switch (featureID)
    {
      case DJPackage.CONSTRUCTOR_SUPER_EXPRESSION__PAR_S:
        return getParS();
    }
    return super.eGet(featureID, resolve, coreType);
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  @SuppressWarnings("unchecked")
  @Override
  public void eSet(int featureID, Object newValue)
  {
    switch (featureID)
    {
      case DJPackage.CONSTRUCTOR_SUPER_EXPRESSION__PAR_S:
        getParS().clear();
        getParS().addAll((Collection<? extends Parameter>)newValue);
        return;
    }
    super.eSet(featureID, newValue);
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  @Override
  public void eUnset(int featureID)
  {
    switch (featureID)
    {
      case DJPackage.CONSTRUCTOR_SUPER_EXPRESSION__PAR_S:
        getParS().clear();
        return;
    }
    super.eUnset(featureID);
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  @Override
  public boolean eIsSet(int featureID)
  {
    switch (featureID)
    {
      case DJPackage.CONSTRUCTOR_SUPER_EXPRESSION__PAR_S:
        return parS != null && !parS.isEmpty();
    }
    return super.eIsSet(featureID);
  }

} //ConstructorSuperExpressionImpl
