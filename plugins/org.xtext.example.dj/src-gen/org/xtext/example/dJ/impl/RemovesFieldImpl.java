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

import org.xtext.example.dJ.DJPackage;
import org.xtext.example.dJ.FieldRef;
import org.xtext.example.dJ.RemovesField;

/**
 * <!-- begin-user-doc -->
 * An implementation of the model object '<em><b>Removes Field</b></em>'.
 * <!-- end-user-doc -->
 * <p>
 * The following features are implemented:
 * <ul>
 *   <li>{@link org.xtext.example.dJ.impl.RemovesFieldImpl#getFieldRef <em>Field Ref</em>}</li>
 * </ul>
 * </p>
 *
 * @generated
 */
public class RemovesFieldImpl extends MinimalEObjectImpl.Container implements RemovesField
{
  /**
   * The cached value of the '{@link #getFieldRef() <em>Field Ref</em>}' reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see #getFieldRef()
   * @generated
   * @ordered
   */
  protected FieldRef fieldRef;

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  protected RemovesFieldImpl()
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
    return DJPackage.Literals.REMOVES_FIELD;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public FieldRef getFieldRef()
  {
    if (fieldRef != null && fieldRef.eIsProxy())
    {
      InternalEObject oldFieldRef = (InternalEObject)fieldRef;
      fieldRef = (FieldRef)eResolveProxy(oldFieldRef);
      if (fieldRef != oldFieldRef)
      {
        if (eNotificationRequired())
          eNotify(new ENotificationImpl(this, Notification.RESOLVE, DJPackage.REMOVES_FIELD__FIELD_REF, oldFieldRef, fieldRef));
      }
    }
    return fieldRef;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public FieldRef basicGetFieldRef()
  {
    return fieldRef;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public void setFieldRef(FieldRef newFieldRef)
  {
    FieldRef oldFieldRef = fieldRef;
    fieldRef = newFieldRef;
    if (eNotificationRequired())
      eNotify(new ENotificationImpl(this, Notification.SET, DJPackage.REMOVES_FIELD__FIELD_REF, oldFieldRef, fieldRef));
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
      case DJPackage.REMOVES_FIELD__FIELD_REF:
        if (resolve) return getFieldRef();
        return basicGetFieldRef();
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
      case DJPackage.REMOVES_FIELD__FIELD_REF:
        setFieldRef((FieldRef)newValue);
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
      case DJPackage.REMOVES_FIELD__FIELD_REF:
        setFieldRef((FieldRef)null);
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
      case DJPackage.REMOVES_FIELD__FIELD_REF:
        return fieldRef != null;
    }
    return super.eIsSet(featureID);
  }

} //RemovesFieldImpl
