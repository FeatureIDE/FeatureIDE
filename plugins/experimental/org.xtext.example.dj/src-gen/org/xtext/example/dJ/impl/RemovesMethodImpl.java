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
import org.xtext.example.dJ.MethodRef;
import org.xtext.example.dJ.RemovesMethod;

/**
 * <!-- begin-user-doc -->
 * An implementation of the model object '<em><b>Removes Method</b></em>'.
 * <!-- end-user-doc -->
 * <p>
 * The following features are implemented:
 * <ul>
 *   <li>{@link org.xtext.example.dJ.impl.RemovesMethodImpl#getMethodRef <em>Method Ref</em>}</li>
 * </ul>
 * </p>
 *
 * @generated
 */
public class RemovesMethodImpl extends MinimalEObjectImpl.Container implements RemovesMethod
{
  /**
   * The cached value of the '{@link #getMethodRef() <em>Method Ref</em>}' reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see #getMethodRef()
   * @generated
   * @ordered
   */
  protected MethodRef methodRef;

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  protected RemovesMethodImpl()
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
    return DJPackage.Literals.REMOVES_METHOD;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public MethodRef getMethodRef()
  {
    if (methodRef != null && methodRef.eIsProxy())
    {
      InternalEObject oldMethodRef = (InternalEObject)methodRef;
      methodRef = (MethodRef)eResolveProxy(oldMethodRef);
      if (methodRef != oldMethodRef)
      {
        if (eNotificationRequired())
          eNotify(new ENotificationImpl(this, Notification.RESOLVE, DJPackage.REMOVES_METHOD__METHOD_REF, oldMethodRef, methodRef));
      }
    }
    return methodRef;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public MethodRef basicGetMethodRef()
  {
    return methodRef;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public void setMethodRef(MethodRef newMethodRef)
  {
    MethodRef oldMethodRef = methodRef;
    methodRef = newMethodRef;
    if (eNotificationRequired())
      eNotify(new ENotificationImpl(this, Notification.SET, DJPackage.REMOVES_METHOD__METHOD_REF, oldMethodRef, methodRef));
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
      case DJPackage.REMOVES_METHOD__METHOD_REF:
        if (resolve) return getMethodRef();
        return basicGetMethodRef();
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
      case DJPackage.REMOVES_METHOD__METHOD_REF:
        setMethodRef((MethodRef)newValue);
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
      case DJPackage.REMOVES_METHOD__METHOD_REF:
        setMethodRef((MethodRef)null);
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
      case DJPackage.REMOVES_METHOD__METHOD_REF:
        return methodRef != null;
    }
    return super.eIsSet(featureID);
  }

} //RemovesMethodImpl
