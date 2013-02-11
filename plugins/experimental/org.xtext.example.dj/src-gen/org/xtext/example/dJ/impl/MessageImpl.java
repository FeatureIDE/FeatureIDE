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
import org.xtext.example.dJ.FieldAccess;
import org.xtext.example.dJ.Message;
import org.xtext.example.dJ.MethodCall;

/**
 * <!-- begin-user-doc -->
 * An implementation of the model object '<em><b>Message</b></em>'.
 * <!-- end-user-doc -->
 * <p>
 * The following features are implemented:
 * <ul>
 *   <li>{@link org.xtext.example.dJ.impl.MessageImpl#getMethodCall <em>Method Call</em>}</li>
 *   <li>{@link org.xtext.example.dJ.impl.MessageImpl#getFieldAccess <em>Field Access</em>}</li>
 * </ul>
 * </p>
 *
 * @generated
 */
public class MessageImpl extends MinimalEObjectImpl.Container implements Message
{
  /**
   * The cached value of the '{@link #getMethodCall() <em>Method Call</em>}' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see #getMethodCall()
   * @generated
   * @ordered
   */
  protected MethodCall methodCall;

  /**
   * The cached value of the '{@link #getFieldAccess() <em>Field Access</em>}' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see #getFieldAccess()
   * @generated
   * @ordered
   */
  protected FieldAccess fieldAccess;

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  protected MessageImpl()
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
    return DJPackage.Literals.MESSAGE;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public MethodCall getMethodCall()
  {
    return methodCall;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public NotificationChain basicSetMethodCall(MethodCall newMethodCall, NotificationChain msgs)
  {
    MethodCall oldMethodCall = methodCall;
    methodCall = newMethodCall;
    if (eNotificationRequired())
    {
      ENotificationImpl notification = new ENotificationImpl(this, Notification.SET, DJPackage.MESSAGE__METHOD_CALL, oldMethodCall, newMethodCall);
      if (msgs == null) msgs = notification; else msgs.add(notification);
    }
    return msgs;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public void setMethodCall(MethodCall newMethodCall)
  {
    if (newMethodCall != methodCall)
    {
      NotificationChain msgs = null;
      if (methodCall != null)
        msgs = ((InternalEObject)methodCall).eInverseRemove(this, EOPPOSITE_FEATURE_BASE - DJPackage.MESSAGE__METHOD_CALL, null, msgs);
      if (newMethodCall != null)
        msgs = ((InternalEObject)newMethodCall).eInverseAdd(this, EOPPOSITE_FEATURE_BASE - DJPackage.MESSAGE__METHOD_CALL, null, msgs);
      msgs = basicSetMethodCall(newMethodCall, msgs);
      if (msgs != null) msgs.dispatch();
    }
    else if (eNotificationRequired())
      eNotify(new ENotificationImpl(this, Notification.SET, DJPackage.MESSAGE__METHOD_CALL, newMethodCall, newMethodCall));
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public FieldAccess getFieldAccess()
  {
    return fieldAccess;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public NotificationChain basicSetFieldAccess(FieldAccess newFieldAccess, NotificationChain msgs)
  {
    FieldAccess oldFieldAccess = fieldAccess;
    fieldAccess = newFieldAccess;
    if (eNotificationRequired())
    {
      ENotificationImpl notification = new ENotificationImpl(this, Notification.SET, DJPackage.MESSAGE__FIELD_ACCESS, oldFieldAccess, newFieldAccess);
      if (msgs == null) msgs = notification; else msgs.add(notification);
    }
    return msgs;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public void setFieldAccess(FieldAccess newFieldAccess)
  {
    if (newFieldAccess != fieldAccess)
    {
      NotificationChain msgs = null;
      if (fieldAccess != null)
        msgs = ((InternalEObject)fieldAccess).eInverseRemove(this, EOPPOSITE_FEATURE_BASE - DJPackage.MESSAGE__FIELD_ACCESS, null, msgs);
      if (newFieldAccess != null)
        msgs = ((InternalEObject)newFieldAccess).eInverseAdd(this, EOPPOSITE_FEATURE_BASE - DJPackage.MESSAGE__FIELD_ACCESS, null, msgs);
      msgs = basicSetFieldAccess(newFieldAccess, msgs);
      if (msgs != null) msgs.dispatch();
    }
    else if (eNotificationRequired())
      eNotify(new ENotificationImpl(this, Notification.SET, DJPackage.MESSAGE__FIELD_ACCESS, newFieldAccess, newFieldAccess));
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
      case DJPackage.MESSAGE__METHOD_CALL:
        return basicSetMethodCall(null, msgs);
      case DJPackage.MESSAGE__FIELD_ACCESS:
        return basicSetFieldAccess(null, msgs);
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
      case DJPackage.MESSAGE__METHOD_CALL:
        return getMethodCall();
      case DJPackage.MESSAGE__FIELD_ACCESS:
        return getFieldAccess();
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
      case DJPackage.MESSAGE__METHOD_CALL:
        setMethodCall((MethodCall)newValue);
        return;
      case DJPackage.MESSAGE__FIELD_ACCESS:
        setFieldAccess((FieldAccess)newValue);
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
      case DJPackage.MESSAGE__METHOD_CALL:
        setMethodCall((MethodCall)null);
        return;
      case DJPackage.MESSAGE__FIELD_ACCESS:
        setFieldAccess((FieldAccess)null);
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
      case DJPackage.MESSAGE__METHOD_CALL:
        return methodCall != null;
      case DJPackage.MESSAGE__FIELD_ACCESS:
        return fieldAccess != null;
    }
    return super.eIsSet(featureID);
  }

} //MessageImpl
