/**
 * <copyright>
 * </copyright>
 *
 */
package org.xtext.example.dJ.impl;

import org.eclipse.emf.common.notify.Notification;
import org.eclipse.emf.common.notify.NotificationChain;

import org.eclipse.emf.ecore.EClass;
import org.eclipse.emf.ecore.InternalEObject;

import org.eclipse.emf.ecore.impl.ENotificationImpl;
import org.eclipse.emf.ecore.impl.MinimalEObjectImpl;

import org.xtext.example.dJ.DJPackage;
import org.xtext.example.dJ.FieldRef;
import org.xtext.example.dJ.RenamesField;

/**
 * <!-- begin-user-doc -->
 * An implementation of the model object '<em><b>Renames Field</b></em>'.
 * <!-- end-user-doc -->
 * <p>
 * The following features are implemented:
 * <ul>
 *   <li>{@link org.xtext.example.dJ.impl.RenamesFieldImpl#getFieldRef <em>Field Ref</em>}</li>
 *   <li>{@link org.xtext.example.dJ.impl.RenamesFieldImpl#getNewFieldRef <em>New Field Ref</em>}</li>
 * </ul>
 * </p>
 *
 * @generated
 */
public class RenamesFieldImpl extends MinimalEObjectImpl.Container implements RenamesField
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
   * The cached value of the '{@link #getNewFieldRef() <em>New Field Ref</em>}' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see #getNewFieldRef()
   * @generated
   * @ordered
   */
  protected FieldRef newFieldRef;

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  protected RenamesFieldImpl()
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
    return DJPackage.Literals.RENAMES_FIELD;
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
          eNotify(new ENotificationImpl(this, Notification.RESOLVE, DJPackage.RENAMES_FIELD__FIELD_REF, oldFieldRef, fieldRef));
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
      eNotify(new ENotificationImpl(this, Notification.SET, DJPackage.RENAMES_FIELD__FIELD_REF, oldFieldRef, fieldRef));
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public FieldRef getNewFieldRef()
  {
    return newFieldRef;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public NotificationChain basicSetNewFieldRef(FieldRef newNewFieldRef, NotificationChain msgs)
  {
    FieldRef oldNewFieldRef = newFieldRef;
    newFieldRef = newNewFieldRef;
    if (eNotificationRequired())
    {
      ENotificationImpl notification = new ENotificationImpl(this, Notification.SET, DJPackage.RENAMES_FIELD__NEW_FIELD_REF, oldNewFieldRef, newNewFieldRef);
      if (msgs == null) msgs = notification; else msgs.add(notification);
    }
    return msgs;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public void setNewFieldRef(FieldRef newNewFieldRef)
  {
    if (newNewFieldRef != newFieldRef)
    {
      NotificationChain msgs = null;
      if (newFieldRef != null)
        msgs = ((InternalEObject)newFieldRef).eInverseRemove(this, EOPPOSITE_FEATURE_BASE - DJPackage.RENAMES_FIELD__NEW_FIELD_REF, null, msgs);
      if (newNewFieldRef != null)
        msgs = ((InternalEObject)newNewFieldRef).eInverseAdd(this, EOPPOSITE_FEATURE_BASE - DJPackage.RENAMES_FIELD__NEW_FIELD_REF, null, msgs);
      msgs = basicSetNewFieldRef(newNewFieldRef, msgs);
      if (msgs != null) msgs.dispatch();
    }
    else if (eNotificationRequired())
      eNotify(new ENotificationImpl(this, Notification.SET, DJPackage.RENAMES_FIELD__NEW_FIELD_REF, newNewFieldRef, newNewFieldRef));
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  @Override
  public NotificationChain eInverseRemove(InternalEObject otherEnd, int featureID, NotificationChain msgs)
  {
    switch (featureID)
    {
      case DJPackage.RENAMES_FIELD__NEW_FIELD_REF:
        return basicSetNewFieldRef(null, msgs);
    }
    return super.eInverseRemove(otherEnd, featureID, msgs);
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
      case DJPackage.RENAMES_FIELD__FIELD_REF:
        if (resolve) return getFieldRef();
        return basicGetFieldRef();
      case DJPackage.RENAMES_FIELD__NEW_FIELD_REF:
        return getNewFieldRef();
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
      case DJPackage.RENAMES_FIELD__FIELD_REF:
        setFieldRef((FieldRef)newValue);
        return;
      case DJPackage.RENAMES_FIELD__NEW_FIELD_REF:
        setNewFieldRef((FieldRef)newValue);
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
      case DJPackage.RENAMES_FIELD__FIELD_REF:
        setFieldRef((FieldRef)null);
        return;
      case DJPackage.RENAMES_FIELD__NEW_FIELD_REF:
        setNewFieldRef((FieldRef)null);
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
      case DJPackage.RENAMES_FIELD__FIELD_REF:
        return fieldRef != null;
      case DJPackage.RENAMES_FIELD__NEW_FIELD_REF:
        return newFieldRef != null;
    }
    return super.eIsSet(featureID);
  }

} //RenamesFieldImpl
