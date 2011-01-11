/**
 * <copyright>
 * </copyright>
 *
 */
package org.xtext.example.dJ.impl;

import org.eclipse.emf.common.notify.Notification;

import org.eclipse.emf.ecore.EClass;
import org.eclipse.emf.ecore.InternalEObject;

import org.eclipse.emf.ecore.impl.ENotificationImpl;
import org.eclipse.emf.ecore.impl.MinimalEObjectImpl;

import org.xtext.example.dJ.ConstructorFieldExpression;
import org.xtext.example.dJ.DJPackage;
import org.xtext.example.dJ.FieldRef;
import org.xtext.example.dJ.Parameter;

/**
 * <!-- begin-user-doc -->
 * An implementation of the model object '<em><b>Constructor Field Expression</b></em>'.
 * <!-- end-user-doc -->
 * <p>
 * The following features are implemented:
 * <ul>
 *   <li>{@link org.xtext.example.dJ.impl.ConstructorFieldExpressionImpl#getField <em>Field</em>}</li>
 *   <li>{@link org.xtext.example.dJ.impl.ConstructorFieldExpressionImpl#getParT <em>Par T</em>}</li>
 * </ul>
 * </p>
 *
 * @generated
 */
public class ConstructorFieldExpressionImpl extends MinimalEObjectImpl.Container implements ConstructorFieldExpression
{
  /**
   * The cached value of the '{@link #getField() <em>Field</em>}' reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see #getField()
   * @generated
   * @ordered
   */
  protected FieldRef field;

  /**
   * The cached value of the '{@link #getParT() <em>Par T</em>}' reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see #getParT()
   * @generated
   * @ordered
   */
  protected Parameter parT;

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  protected ConstructorFieldExpressionImpl()
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
    return DJPackage.Literals.CONSTRUCTOR_FIELD_EXPRESSION;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public FieldRef getField()
  {
    if (field != null && field.eIsProxy())
    {
      InternalEObject oldField = (InternalEObject)field;
      field = (FieldRef)eResolveProxy(oldField);
      if (field != oldField)
      {
        if (eNotificationRequired())
          eNotify(new ENotificationImpl(this, Notification.RESOLVE, DJPackage.CONSTRUCTOR_FIELD_EXPRESSION__FIELD, oldField, field));
      }
    }
    return field;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public FieldRef basicGetField()
  {
    return field;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public void setField(FieldRef newField)
  {
    FieldRef oldField = field;
    field = newField;
    if (eNotificationRequired())
      eNotify(new ENotificationImpl(this, Notification.SET, DJPackage.CONSTRUCTOR_FIELD_EXPRESSION__FIELD, oldField, field));
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public Parameter getParT()
  {
    if (parT != null && parT.eIsProxy())
    {
      InternalEObject oldParT = (InternalEObject)parT;
      parT = (Parameter)eResolveProxy(oldParT);
      if (parT != oldParT)
      {
        if (eNotificationRequired())
          eNotify(new ENotificationImpl(this, Notification.RESOLVE, DJPackage.CONSTRUCTOR_FIELD_EXPRESSION__PAR_T, oldParT, parT));
      }
    }
    return parT;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public Parameter basicGetParT()
  {
    return parT;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public void setParT(Parameter newParT)
  {
    Parameter oldParT = parT;
    parT = newParT;
    if (eNotificationRequired())
      eNotify(new ENotificationImpl(this, Notification.SET, DJPackage.CONSTRUCTOR_FIELD_EXPRESSION__PAR_T, oldParT, parT));
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
      case DJPackage.CONSTRUCTOR_FIELD_EXPRESSION__FIELD:
        if (resolve) return getField();
        return basicGetField();
      case DJPackage.CONSTRUCTOR_FIELD_EXPRESSION__PAR_T:
        if (resolve) return getParT();
        return basicGetParT();
    }
    return super.eGet(featureID, resolve, coreType);
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  @Override
  public void eSet(int featureID, Object newValue)
  {
    switch (featureID)
    {
      case DJPackage.CONSTRUCTOR_FIELD_EXPRESSION__FIELD:
        setField((FieldRef)newValue);
        return;
      case DJPackage.CONSTRUCTOR_FIELD_EXPRESSION__PAR_T:
        setParT((Parameter)newValue);
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
      case DJPackage.CONSTRUCTOR_FIELD_EXPRESSION__FIELD:
        setField((FieldRef)null);
        return;
      case DJPackage.CONSTRUCTOR_FIELD_EXPRESSION__PAR_T:
        setParT((Parameter)null);
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
      case DJPackage.CONSTRUCTOR_FIELD_EXPRESSION__FIELD:
        return field != null;
      case DJPackage.CONSTRUCTOR_FIELD_EXPRESSION__PAR_T:
        return parT != null;
    }
    return super.eIsSet(featureID);
  }

} //ConstructorFieldExpressionImpl
