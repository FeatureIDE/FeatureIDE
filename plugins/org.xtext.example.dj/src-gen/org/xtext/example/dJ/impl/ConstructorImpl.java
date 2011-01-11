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

import org.xtext.example.dJ.Constructor;
import org.xtext.example.dJ.ConstructorFieldExpression;
import org.xtext.example.dJ.ConstructorSuperExpression;
import org.xtext.example.dJ.DJPackage;
import org.xtext.example.dJ.Parameter;

/**
 * <!-- begin-user-doc -->
 * An implementation of the model object '<em><b>Constructor</b></em>'.
 * <!-- end-user-doc -->
 * <p>
 * The following features are implemented:
 * <ul>
 *   <li>{@link org.xtext.example.dJ.impl.ConstructorImpl#getName <em>Name</em>}</li>
 *   <li>{@link org.xtext.example.dJ.impl.ConstructorImpl#getParams <em>Params</em>}</li>
 *   <li>{@link org.xtext.example.dJ.impl.ConstructorImpl#getConstructorSuperExpression <em>Constructor Super Expression</em>}</li>
 *   <li>{@link org.xtext.example.dJ.impl.ConstructorImpl#getConstructorFieldExpression <em>Constructor Field Expression</em>}</li>
 * </ul>
 * </p>
 *
 * @generated
 */
public class ConstructorImpl extends MinimalEObjectImpl.Container implements Constructor
{
  /**
   * The cached value of the '{@link #getName() <em>Name</em>}' reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see #getName()
   * @generated
   * @ordered
   */
  protected org.xtext.example.dJ.Class name;

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
   * The cached value of the '{@link #getConstructorSuperExpression() <em>Constructor Super Expression</em>}' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see #getConstructorSuperExpression()
   * @generated
   * @ordered
   */
  protected ConstructorSuperExpression constructorSuperExpression;

  /**
   * The cached value of the '{@link #getConstructorFieldExpression() <em>Constructor Field Expression</em>}' containment reference list.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see #getConstructorFieldExpression()
   * @generated
   * @ordered
   */
  protected EList<ConstructorFieldExpression> constructorFieldExpression;

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  protected ConstructorImpl()
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
    return DJPackage.Literals.CONSTRUCTOR;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public org.xtext.example.dJ.Class getName()
  {
    if (name != null && name.eIsProxy())
    {
      InternalEObject oldName = (InternalEObject)name;
      name = (org.xtext.example.dJ.Class)eResolveProxy(oldName);
      if (name != oldName)
      {
        if (eNotificationRequired())
          eNotify(new ENotificationImpl(this, Notification.RESOLVE, DJPackage.CONSTRUCTOR__NAME, oldName, name));
      }
    }
    return name;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public org.xtext.example.dJ.Class basicGetName()
  {
    return name;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public void setName(org.xtext.example.dJ.Class newName)
  {
    org.xtext.example.dJ.Class oldName = name;
    name = newName;
    if (eNotificationRequired())
      eNotify(new ENotificationImpl(this, Notification.SET, DJPackage.CONSTRUCTOR__NAME, oldName, name));
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
      params = new EObjectContainmentEList<Parameter>(Parameter.class, this, DJPackage.CONSTRUCTOR__PARAMS);
    }
    return params;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public ConstructorSuperExpression getConstructorSuperExpression()
  {
    return constructorSuperExpression;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public NotificationChain basicSetConstructorSuperExpression(ConstructorSuperExpression newConstructorSuperExpression, NotificationChain msgs)
  {
    ConstructorSuperExpression oldConstructorSuperExpression = constructorSuperExpression;
    constructorSuperExpression = newConstructorSuperExpression;
    if (eNotificationRequired())
    {
      ENotificationImpl notification = new ENotificationImpl(this, Notification.SET, DJPackage.CONSTRUCTOR__CONSTRUCTOR_SUPER_EXPRESSION, oldConstructorSuperExpression, newConstructorSuperExpression);
      if (msgs == null) msgs = notification; else msgs.add(notification);
    }
    return msgs;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public void setConstructorSuperExpression(ConstructorSuperExpression newConstructorSuperExpression)
  {
    if (newConstructorSuperExpression != constructorSuperExpression)
    {
      NotificationChain msgs = null;
      if (constructorSuperExpression != null)
        msgs = ((InternalEObject)constructorSuperExpression).eInverseRemove(this, EOPPOSITE_FEATURE_BASE - DJPackage.CONSTRUCTOR__CONSTRUCTOR_SUPER_EXPRESSION, null, msgs);
      if (newConstructorSuperExpression != null)
        msgs = ((InternalEObject)newConstructorSuperExpression).eInverseAdd(this, EOPPOSITE_FEATURE_BASE - DJPackage.CONSTRUCTOR__CONSTRUCTOR_SUPER_EXPRESSION, null, msgs);
      msgs = basicSetConstructorSuperExpression(newConstructorSuperExpression, msgs);
      if (msgs != null) msgs.dispatch();
    }
    else if (eNotificationRequired())
      eNotify(new ENotificationImpl(this, Notification.SET, DJPackage.CONSTRUCTOR__CONSTRUCTOR_SUPER_EXPRESSION, newConstructorSuperExpression, newConstructorSuperExpression));
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public EList<ConstructorFieldExpression> getConstructorFieldExpression()
  {
    if (constructorFieldExpression == null)
    {
      constructorFieldExpression = new EObjectContainmentEList<ConstructorFieldExpression>(ConstructorFieldExpression.class, this, DJPackage.CONSTRUCTOR__CONSTRUCTOR_FIELD_EXPRESSION);
    }
    return constructorFieldExpression;
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
      case DJPackage.CONSTRUCTOR__PARAMS:
        return ((InternalEList<?>)getParams()).basicRemove(otherEnd, msgs);
      case DJPackage.CONSTRUCTOR__CONSTRUCTOR_SUPER_EXPRESSION:
        return basicSetConstructorSuperExpression(null, msgs);
      case DJPackage.CONSTRUCTOR__CONSTRUCTOR_FIELD_EXPRESSION:
        return ((InternalEList<?>)getConstructorFieldExpression()).basicRemove(otherEnd, msgs);
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
      case DJPackage.CONSTRUCTOR__NAME:
        if (resolve) return getName();
        return basicGetName();
      case DJPackage.CONSTRUCTOR__PARAMS:
        return getParams();
      case DJPackage.CONSTRUCTOR__CONSTRUCTOR_SUPER_EXPRESSION:
        return getConstructorSuperExpression();
      case DJPackage.CONSTRUCTOR__CONSTRUCTOR_FIELD_EXPRESSION:
        return getConstructorFieldExpression();
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
      case DJPackage.CONSTRUCTOR__NAME:
        setName((org.xtext.example.dJ.Class)newValue);
        return;
      case DJPackage.CONSTRUCTOR__PARAMS:
        getParams().clear();
        getParams().addAll((Collection<? extends Parameter>)newValue);
        return;
      case DJPackage.CONSTRUCTOR__CONSTRUCTOR_SUPER_EXPRESSION:
        setConstructorSuperExpression((ConstructorSuperExpression)newValue);
        return;
      case DJPackage.CONSTRUCTOR__CONSTRUCTOR_FIELD_EXPRESSION:
        getConstructorFieldExpression().clear();
        getConstructorFieldExpression().addAll((Collection<? extends ConstructorFieldExpression>)newValue);
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
      case DJPackage.CONSTRUCTOR__NAME:
        setName((org.xtext.example.dJ.Class)null);
        return;
      case DJPackage.CONSTRUCTOR__PARAMS:
        getParams().clear();
        return;
      case DJPackage.CONSTRUCTOR__CONSTRUCTOR_SUPER_EXPRESSION:
        setConstructorSuperExpression((ConstructorSuperExpression)null);
        return;
      case DJPackage.CONSTRUCTOR__CONSTRUCTOR_FIELD_EXPRESSION:
        getConstructorFieldExpression().clear();
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
      case DJPackage.CONSTRUCTOR__NAME:
        return name != null;
      case DJPackage.CONSTRUCTOR__PARAMS:
        return params != null && !params.isEmpty();
      case DJPackage.CONSTRUCTOR__CONSTRUCTOR_SUPER_EXPRESSION:
        return constructorSuperExpression != null;
      case DJPackage.CONSTRUCTOR__CONSTRUCTOR_FIELD_EXPRESSION:
        return constructorFieldExpression != null && !constructorFieldExpression.isEmpty();
    }
    return super.eIsSet(featureID);
  }

} //ConstructorImpl
