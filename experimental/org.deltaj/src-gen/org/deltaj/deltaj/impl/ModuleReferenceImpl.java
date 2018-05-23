/**
 * <copyright>
 * </copyright>
 *
 */
package org.deltaj.deltaj.impl;

import org.deltaj.deltaj.DeltaModule;
import org.deltaj.deltaj.DeltajPackage;
import org.deltaj.deltaj.ModuleReference;
import org.deltaj.deltaj.PropositionalFormula;

import org.eclipse.emf.common.notify.Notification;
import org.eclipse.emf.common.notify.NotificationChain;

import org.eclipse.emf.ecore.EClass;
import org.eclipse.emf.ecore.InternalEObject;

import org.eclipse.emf.ecore.impl.ENotificationImpl;
import org.eclipse.emf.ecore.impl.MinimalEObjectImpl;

/**
 * <!-- begin-user-doc -->
 * An implementation of the model object '<em><b>Module Reference</b></em>'.
 * <!-- end-user-doc -->
 * <p>
 * The following features are implemented:
 * <ul>
 *   <li>{@link org.deltaj.deltaj.impl.ModuleReferenceImpl#getDeltaModule <em>Delta Module</em>}</li>
 *   <li>{@link org.deltaj.deltaj.impl.ModuleReferenceImpl#getWhen <em>When</em>}</li>
 * </ul>
 * </p>
 *
 * @generated
 */
public class ModuleReferenceImpl extends MinimalEObjectImpl.Container implements ModuleReference
{
  /**
   * The cached value of the '{@link #getDeltaModule() <em>Delta Module</em>}' reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see #getDeltaModule()
   * @generated
   * @ordered
   */
  protected DeltaModule deltaModule;

  /**
   * The cached value of the '{@link #getWhen() <em>When</em>}' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see #getWhen()
   * @generated
   * @ordered
   */
  protected PropositionalFormula when;

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  protected ModuleReferenceImpl()
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
    return DeltajPackage.Literals.MODULE_REFERENCE;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public DeltaModule getDeltaModule()
  {
    if (deltaModule != null && deltaModule.eIsProxy())
    {
      InternalEObject oldDeltaModule = (InternalEObject)deltaModule;
      deltaModule = (DeltaModule)eResolveProxy(oldDeltaModule);
      if (deltaModule != oldDeltaModule)
      {
        if (eNotificationRequired())
          eNotify(new ENotificationImpl(this, Notification.RESOLVE, DeltajPackage.MODULE_REFERENCE__DELTA_MODULE, oldDeltaModule, deltaModule));
      }
    }
    return deltaModule;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public DeltaModule basicGetDeltaModule()
  {
    return deltaModule;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public void setDeltaModule(DeltaModule newDeltaModule)
  {
    DeltaModule oldDeltaModule = deltaModule;
    deltaModule = newDeltaModule;
    if (eNotificationRequired())
      eNotify(new ENotificationImpl(this, Notification.SET, DeltajPackage.MODULE_REFERENCE__DELTA_MODULE, oldDeltaModule, deltaModule));
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public PropositionalFormula getWhen()
  {
    return when;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public NotificationChain basicSetWhen(PropositionalFormula newWhen, NotificationChain msgs)
  {
    PropositionalFormula oldWhen = when;
    when = newWhen;
    if (eNotificationRequired())
    {
      ENotificationImpl notification = new ENotificationImpl(this, Notification.SET, DeltajPackage.MODULE_REFERENCE__WHEN, oldWhen, newWhen);
      if (msgs == null) msgs = notification; else msgs.add(notification);
    }
    return msgs;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public void setWhen(PropositionalFormula newWhen)
  {
    if (newWhen != when)
    {
      NotificationChain msgs = null;
      if (when != null)
        msgs = ((InternalEObject)when).eInverseRemove(this, EOPPOSITE_FEATURE_BASE - DeltajPackage.MODULE_REFERENCE__WHEN, null, msgs);
      if (newWhen != null)
        msgs = ((InternalEObject)newWhen).eInverseAdd(this, EOPPOSITE_FEATURE_BASE - DeltajPackage.MODULE_REFERENCE__WHEN, null, msgs);
      msgs = basicSetWhen(newWhen, msgs);
      if (msgs != null) msgs.dispatch();
    }
    else if (eNotificationRequired())
      eNotify(new ENotificationImpl(this, Notification.SET, DeltajPackage.MODULE_REFERENCE__WHEN, newWhen, newWhen));
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
      case DeltajPackage.MODULE_REFERENCE__WHEN:
        return basicSetWhen(null, msgs);
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
      case DeltajPackage.MODULE_REFERENCE__DELTA_MODULE:
        if (resolve) return getDeltaModule();
        return basicGetDeltaModule();
      case DeltajPackage.MODULE_REFERENCE__WHEN:
        return getWhen();
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
      case DeltajPackage.MODULE_REFERENCE__DELTA_MODULE:
        setDeltaModule((DeltaModule)newValue);
        return;
      case DeltajPackage.MODULE_REFERENCE__WHEN:
        setWhen((PropositionalFormula)newValue);
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
      case DeltajPackage.MODULE_REFERENCE__DELTA_MODULE:
        setDeltaModule((DeltaModule)null);
        return;
      case DeltajPackage.MODULE_REFERENCE__WHEN:
        setWhen((PropositionalFormula)null);
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
      case DeltajPackage.MODULE_REFERENCE__DELTA_MODULE:
        return deltaModule != null;
      case DeltajPackage.MODULE_REFERENCE__WHEN:
        return when != null;
    }
    return super.eIsSet(featureID);
  }

} //ModuleReferenceImpl
