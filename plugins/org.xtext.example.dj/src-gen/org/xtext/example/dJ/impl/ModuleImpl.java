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

import org.xtext.example.dJ.Core;
import org.xtext.example.dJ.DJPackage;
import org.xtext.example.dJ.Delta;
import org.xtext.example.dJ.Module;

/**
 * <!-- begin-user-doc -->
 * An implementation of the model object '<em><b>Module</b></em>'.
 * <!-- end-user-doc -->
 * <p>
 * The following features are implemented:
 * <ul>
 *   <li>{@link org.xtext.example.dJ.impl.ModuleImpl#getNtype <em>Ntype</em>}</li>
 *   <li>{@link org.xtext.example.dJ.impl.ModuleImpl#getCore <em>Core</em>}</li>
 *   <li>{@link org.xtext.example.dJ.impl.ModuleImpl#getDelta <em>Delta</em>}</li>
 * </ul>
 * </p>
 *
 * @generated
 */
public class ModuleImpl extends MinimalEObjectImpl.Container implements Module
{
  /**
   * The default value of the '{@link #getNtype() <em>Ntype</em>}' attribute.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see #getNtype()
   * @generated
   * @ordered
   */
  protected static final String NTYPE_EDEFAULT = null;

  /**
   * The cached value of the '{@link #getNtype() <em>Ntype</em>}' attribute.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see #getNtype()
   * @generated
   * @ordered
   */
  protected String ntype = NTYPE_EDEFAULT;

  /**
   * The cached value of the '{@link #getCore() <em>Core</em>}' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see #getCore()
   * @generated
   * @ordered
   */
  protected Core core;

  /**
   * The cached value of the '{@link #getDelta() <em>Delta</em>}' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see #getDelta()
   * @generated
   * @ordered
   */
  protected Delta delta;

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  protected ModuleImpl()
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
    return DJPackage.Literals.MODULE;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public String getNtype()
  {
    return ntype;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public void setNtype(String newNtype)
  {
    String oldNtype = ntype;
    ntype = newNtype;
    if (eNotificationRequired())
      eNotify(new ENotificationImpl(this, Notification.SET, DJPackage.MODULE__NTYPE, oldNtype, ntype));
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public Core getCore()
  {
    return core;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public NotificationChain basicSetCore(Core newCore, NotificationChain msgs)
  {
    Core oldCore = core;
    core = newCore;
    if (eNotificationRequired())
    {
      ENotificationImpl notification = new ENotificationImpl(this, Notification.SET, DJPackage.MODULE__CORE, oldCore, newCore);
      if (msgs == null) msgs = notification; else msgs.add(notification);
    }
    return msgs;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public void setCore(Core newCore)
  {
    if (newCore != core)
    {
      NotificationChain msgs = null;
      if (core != null)
        msgs = ((InternalEObject)core).eInverseRemove(this, EOPPOSITE_FEATURE_BASE - DJPackage.MODULE__CORE, null, msgs);
      if (newCore != null)
        msgs = ((InternalEObject)newCore).eInverseAdd(this, EOPPOSITE_FEATURE_BASE - DJPackage.MODULE__CORE, null, msgs);
      msgs = basicSetCore(newCore, msgs);
      if (msgs != null) msgs.dispatch();
    }
    else if (eNotificationRequired())
      eNotify(new ENotificationImpl(this, Notification.SET, DJPackage.MODULE__CORE, newCore, newCore));
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public Delta getDelta()
  {
    return delta;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public NotificationChain basicSetDelta(Delta newDelta, NotificationChain msgs)
  {
    Delta oldDelta = delta;
    delta = newDelta;
    if (eNotificationRequired())
    {
      ENotificationImpl notification = new ENotificationImpl(this, Notification.SET, DJPackage.MODULE__DELTA, oldDelta, newDelta);
      if (msgs == null) msgs = notification; else msgs.add(notification);
    }
    return msgs;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public void setDelta(Delta newDelta)
  {
    if (newDelta != delta)
    {
      NotificationChain msgs = null;
      if (delta != null)
        msgs = ((InternalEObject)delta).eInverseRemove(this, EOPPOSITE_FEATURE_BASE - DJPackage.MODULE__DELTA, null, msgs);
      if (newDelta != null)
        msgs = ((InternalEObject)newDelta).eInverseAdd(this, EOPPOSITE_FEATURE_BASE - DJPackage.MODULE__DELTA, null, msgs);
      msgs = basicSetDelta(newDelta, msgs);
      if (msgs != null) msgs.dispatch();
    }
    else if (eNotificationRequired())
      eNotify(new ENotificationImpl(this, Notification.SET, DJPackage.MODULE__DELTA, newDelta, newDelta));
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
      case DJPackage.MODULE__CORE:
        return basicSetCore(null, msgs);
      case DJPackage.MODULE__DELTA:
        return basicSetDelta(null, msgs);
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
      case DJPackage.MODULE__NTYPE:
        return getNtype();
      case DJPackage.MODULE__CORE:
        return getCore();
      case DJPackage.MODULE__DELTA:
        return getDelta();
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
      case DJPackage.MODULE__NTYPE:
        setNtype((String)newValue);
        return;
      case DJPackage.MODULE__CORE:
        setCore((Core)newValue);
        return;
      case DJPackage.MODULE__DELTA:
        setDelta((Delta)newValue);
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
      case DJPackage.MODULE__NTYPE:
        setNtype(NTYPE_EDEFAULT);
        return;
      case DJPackage.MODULE__CORE:
        setCore((Core)null);
        return;
      case DJPackage.MODULE__DELTA:
        setDelta((Delta)null);
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
      case DJPackage.MODULE__NTYPE:
        return NTYPE_EDEFAULT == null ? ntype != null : !NTYPE_EDEFAULT.equals(ntype);
      case DJPackage.MODULE__CORE:
        return core != null;
      case DJPackage.MODULE__DELTA:
        return delta != null;
    }
    return super.eIsSet(featureID);
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  @Override
  public String toString()
  {
    if (eIsProxy()) return super.toString();

    StringBuffer result = new StringBuffer(super.toString());
    result.append(" (ntype: ");
    result.append(ntype);
    result.append(')');
    return result.toString();
  }

} //ModuleImpl
