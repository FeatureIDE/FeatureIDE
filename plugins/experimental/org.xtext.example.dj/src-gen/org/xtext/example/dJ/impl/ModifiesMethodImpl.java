/**
 * <copyright>
 * </copyright>
 *
 */
package org.xtext.example.dJ.impl;

import java.util.Collection;

import org.eclipse.emf.common.notify.Notification;
import org.eclipse.emf.common.notify.NotificationChain;

import org.eclipse.emf.common.util.EList;

import org.eclipse.emf.ecore.EClass;
import org.eclipse.emf.ecore.InternalEObject;

import org.eclipse.emf.ecore.impl.ENotificationImpl;
import org.eclipse.emf.ecore.impl.MinimalEObjectImpl;

import org.eclipse.emf.ecore.util.EObjectContainmentEList;
import org.eclipse.emf.ecore.util.InternalEList;

import org.xtext.example.dJ.DJPackage;
import org.xtext.example.dJ.MethodBody;
import org.xtext.example.dJ.MethodRef;
import org.xtext.example.dJ.ModifiesMethod;
import org.xtext.example.dJ.Parameter;
import org.xtext.example.dJ.Type;

/**
 * <!-- begin-user-doc -->
 * An implementation of the model object '<em><b>Modifies Method</b></em>'.
 * <!-- end-user-doc -->
 * <p>
 * The following features are implemented:
 * <ul>
 *   <li>{@link org.xtext.example.dJ.impl.ModifiesMethodImpl#getReturntype <em>Returntype</em>}</li>
 *   <li>{@link org.xtext.example.dJ.impl.ModifiesMethodImpl#getMethodRef <em>Method Ref</em>}</li>
 *   <li>{@link org.xtext.example.dJ.impl.ModifiesMethodImpl#getParams <em>Params</em>}</li>
 *   <li>{@link org.xtext.example.dJ.impl.ModifiesMethodImpl#getBody <em>Body</em>}</li>
 * </ul>
 * </p>
 *
 * @generated
 */
public class ModifiesMethodImpl extends MinimalEObjectImpl.Container implements ModifiesMethod
{
  /**
   * The cached value of the '{@link #getReturntype() <em>Returntype</em>}' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see #getReturntype()
   * @generated
   * @ordered
   */
  protected Type returntype;

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
   * The cached value of the '{@link #getParams() <em>Params</em>}' containment reference list.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see #getParams()
   * @generated
   * @ordered
   */
  protected EList<Parameter> params;

  /**
   * The cached value of the '{@link #getBody() <em>Body</em>}' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see #getBody()
   * @generated
   * @ordered
   */
  protected MethodBody body;

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  protected ModifiesMethodImpl()
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
    return DJPackage.Literals.MODIFIES_METHOD;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public Type getReturntype()
  {
    return returntype;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public NotificationChain basicSetReturntype(Type newReturntype, NotificationChain msgs)
  {
    Type oldReturntype = returntype;
    returntype = newReturntype;
    if (eNotificationRequired())
    {
      ENotificationImpl notification = new ENotificationImpl(this, Notification.SET, DJPackage.MODIFIES_METHOD__RETURNTYPE, oldReturntype, newReturntype);
      if (msgs == null) msgs = notification; else msgs.add(notification);
    }
    return msgs;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public void setReturntype(Type newReturntype)
  {
    if (newReturntype != returntype)
    {
      NotificationChain msgs = null;
      if (returntype != null)
        msgs = ((InternalEObject)returntype).eInverseRemove(this, EOPPOSITE_FEATURE_BASE - DJPackage.MODIFIES_METHOD__RETURNTYPE, null, msgs);
      if (newReturntype != null)
        msgs = ((InternalEObject)newReturntype).eInverseAdd(this, EOPPOSITE_FEATURE_BASE - DJPackage.MODIFIES_METHOD__RETURNTYPE, null, msgs);
      msgs = basicSetReturntype(newReturntype, msgs);
      if (msgs != null) msgs.dispatch();
    }
    else if (eNotificationRequired())
      eNotify(new ENotificationImpl(this, Notification.SET, DJPackage.MODIFIES_METHOD__RETURNTYPE, newReturntype, newReturntype));
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
          eNotify(new ENotificationImpl(this, Notification.RESOLVE, DJPackage.MODIFIES_METHOD__METHOD_REF, oldMethodRef, methodRef));
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
      eNotify(new ENotificationImpl(this, Notification.SET, DJPackage.MODIFIES_METHOD__METHOD_REF, oldMethodRef, methodRef));
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public EList<Parameter> getParams()
  {
    if (params == null)
    {
      params = new EObjectContainmentEList<Parameter>(Parameter.class, this, DJPackage.MODIFIES_METHOD__PARAMS);
    }
    return params;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public MethodBody getBody()
  {
    return body;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public NotificationChain basicSetBody(MethodBody newBody, NotificationChain msgs)
  {
    MethodBody oldBody = body;
    body = newBody;
    if (eNotificationRequired())
    {
      ENotificationImpl notification = new ENotificationImpl(this, Notification.SET, DJPackage.MODIFIES_METHOD__BODY, oldBody, newBody);
      if (msgs == null) msgs = notification; else msgs.add(notification);
    }
    return msgs;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public void setBody(MethodBody newBody)
  {
    if (newBody != body)
    {
      NotificationChain msgs = null;
      if (body != null)
        msgs = ((InternalEObject)body).eInverseRemove(this, EOPPOSITE_FEATURE_BASE - DJPackage.MODIFIES_METHOD__BODY, null, msgs);
      if (newBody != null)
        msgs = ((InternalEObject)newBody).eInverseAdd(this, EOPPOSITE_FEATURE_BASE - DJPackage.MODIFIES_METHOD__BODY, null, msgs);
      msgs = basicSetBody(newBody, msgs);
      if (msgs != null) msgs.dispatch();
    }
    else if (eNotificationRequired())
      eNotify(new ENotificationImpl(this, Notification.SET, DJPackage.MODIFIES_METHOD__BODY, newBody, newBody));
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
      case DJPackage.MODIFIES_METHOD__RETURNTYPE:
        return basicSetReturntype(null, msgs);
      case DJPackage.MODIFIES_METHOD__PARAMS:
        return ((InternalEList<?>)getParams()).basicRemove(otherEnd, msgs);
      case DJPackage.MODIFIES_METHOD__BODY:
        return basicSetBody(null, msgs);
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
      case DJPackage.MODIFIES_METHOD__RETURNTYPE:
        return getReturntype();
      case DJPackage.MODIFIES_METHOD__METHOD_REF:
        if (resolve) return getMethodRef();
        return basicGetMethodRef();
      case DJPackage.MODIFIES_METHOD__PARAMS:
        return getParams();
      case DJPackage.MODIFIES_METHOD__BODY:
        return getBody();
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
      case DJPackage.MODIFIES_METHOD__RETURNTYPE:
        setReturntype((Type)newValue);
        return;
      case DJPackage.MODIFIES_METHOD__METHOD_REF:
        setMethodRef((MethodRef)newValue);
        return;
      case DJPackage.MODIFIES_METHOD__PARAMS:
        getParams().clear();
        getParams().addAll((Collection<? extends Parameter>)newValue);
        return;
      case DJPackage.MODIFIES_METHOD__BODY:
        setBody((MethodBody)newValue);
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
      case DJPackage.MODIFIES_METHOD__RETURNTYPE:
        setReturntype((Type)null);
        return;
      case DJPackage.MODIFIES_METHOD__METHOD_REF:
        setMethodRef((MethodRef)null);
        return;
      case DJPackage.MODIFIES_METHOD__PARAMS:
        getParams().clear();
        return;
      case DJPackage.MODIFIES_METHOD__BODY:
        setBody((MethodBody)null);
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
      case DJPackage.MODIFIES_METHOD__RETURNTYPE:
        return returntype != null;
      case DJPackage.MODIFIES_METHOD__METHOD_REF:
        return methodRef != null;
      case DJPackage.MODIFIES_METHOD__PARAMS:
        return params != null && !params.isEmpty();
      case DJPackage.MODIFIES_METHOD__BODY:
        return body != null;
    }
    return super.eIsSet(featureID);
  }

} //ModifiesMethodImpl
