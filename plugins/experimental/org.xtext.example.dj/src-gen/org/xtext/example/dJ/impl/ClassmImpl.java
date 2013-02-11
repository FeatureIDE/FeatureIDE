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

import org.xtext.example.dJ.AddsClass;
import org.xtext.example.dJ.Classm;
import org.xtext.example.dJ.DJPackage;
import org.xtext.example.dJ.ModifiesClass;
import org.xtext.example.dJ.RemoveClass;

/**
 * <!-- begin-user-doc -->
 * An implementation of the model object '<em><b>Classm</b></em>'.
 * <!-- end-user-doc -->
 * <p>
 * The following features are implemented:
 * <ul>
 *   <li>{@link org.xtext.example.dJ.impl.ClassmImpl#getAction <em>Action</em>}</li>
 *   <li>{@link org.xtext.example.dJ.impl.ClassmImpl#getModifies <em>Modifies</em>}</li>
 *   <li>{@link org.xtext.example.dJ.impl.ClassmImpl#getAdds <em>Adds</em>}</li>
 *   <li>{@link org.xtext.example.dJ.impl.ClassmImpl#getRemove <em>Remove</em>}</li>
 * </ul>
 * </p>
 *
 * @generated
 */
public class ClassmImpl extends MinimalEObjectImpl.Container implements Classm
{
  /**
   * The default value of the '{@link #getAction() <em>Action</em>}' attribute.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see #getAction()
   * @generated
   * @ordered
   */
  protected static final String ACTION_EDEFAULT = null;

  /**
   * The cached value of the '{@link #getAction() <em>Action</em>}' attribute.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see #getAction()
   * @generated
   * @ordered
   */
  protected String action = ACTION_EDEFAULT;

  /**
   * The cached value of the '{@link #getModifies() <em>Modifies</em>}' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see #getModifies()
   * @generated
   * @ordered
   */
  protected ModifiesClass modifies;

  /**
   * The cached value of the '{@link #getAdds() <em>Adds</em>}' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see #getAdds()
   * @generated
   * @ordered
   */
  protected AddsClass adds;

  /**
   * The cached value of the '{@link #getRemove() <em>Remove</em>}' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see #getRemove()
   * @generated
   * @ordered
   */
  protected RemoveClass remove;

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  protected ClassmImpl()
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
    return DJPackage.Literals.CLASSM;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public String getAction()
  {
    return action;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public void setAction(String newAction)
  {
    String oldAction = action;
    action = newAction;
    if (eNotificationRequired())
      eNotify(new ENotificationImpl(this, Notification.SET, DJPackage.CLASSM__ACTION, oldAction, action));
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public ModifiesClass getModifies()
  {
    return modifies;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public NotificationChain basicSetModifies(ModifiesClass newModifies, NotificationChain msgs)
  {
    ModifiesClass oldModifies = modifies;
    modifies = newModifies;
    if (eNotificationRequired())
    {
      ENotificationImpl notification = new ENotificationImpl(this, Notification.SET, DJPackage.CLASSM__MODIFIES, oldModifies, newModifies);
      if (msgs == null) msgs = notification; else msgs.add(notification);
    }
    return msgs;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public void setModifies(ModifiesClass newModifies)
  {
    if (newModifies != modifies)
    {
      NotificationChain msgs = null;
      if (modifies != null)
        msgs = ((InternalEObject)modifies).eInverseRemove(this, EOPPOSITE_FEATURE_BASE - DJPackage.CLASSM__MODIFIES, null, msgs);
      if (newModifies != null)
        msgs = ((InternalEObject)newModifies).eInverseAdd(this, EOPPOSITE_FEATURE_BASE - DJPackage.CLASSM__MODIFIES, null, msgs);
      msgs = basicSetModifies(newModifies, msgs);
      if (msgs != null) msgs.dispatch();
    }
    else if (eNotificationRequired())
      eNotify(new ENotificationImpl(this, Notification.SET, DJPackage.CLASSM__MODIFIES, newModifies, newModifies));
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public AddsClass getAdds()
  {
    return adds;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public NotificationChain basicSetAdds(AddsClass newAdds, NotificationChain msgs)
  {
    AddsClass oldAdds = adds;
    adds = newAdds;
    if (eNotificationRequired())
    {
      ENotificationImpl notification = new ENotificationImpl(this, Notification.SET, DJPackage.CLASSM__ADDS, oldAdds, newAdds);
      if (msgs == null) msgs = notification; else msgs.add(notification);
    }
    return msgs;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public void setAdds(AddsClass newAdds)
  {
    if (newAdds != adds)
    {
      NotificationChain msgs = null;
      if (adds != null)
        msgs = ((InternalEObject)adds).eInverseRemove(this, EOPPOSITE_FEATURE_BASE - DJPackage.CLASSM__ADDS, null, msgs);
      if (newAdds != null)
        msgs = ((InternalEObject)newAdds).eInverseAdd(this, EOPPOSITE_FEATURE_BASE - DJPackage.CLASSM__ADDS, null, msgs);
      msgs = basicSetAdds(newAdds, msgs);
      if (msgs != null) msgs.dispatch();
    }
    else if (eNotificationRequired())
      eNotify(new ENotificationImpl(this, Notification.SET, DJPackage.CLASSM__ADDS, newAdds, newAdds));
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public RemoveClass getRemove()
  {
    return remove;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public NotificationChain basicSetRemove(RemoveClass newRemove, NotificationChain msgs)
  {
    RemoveClass oldRemove = remove;
    remove = newRemove;
    if (eNotificationRequired())
    {
      ENotificationImpl notification = new ENotificationImpl(this, Notification.SET, DJPackage.CLASSM__REMOVE, oldRemove, newRemove);
      if (msgs == null) msgs = notification; else msgs.add(notification);
    }
    return msgs;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public void setRemove(RemoveClass newRemove)
  {
    if (newRemove != remove)
    {
      NotificationChain msgs = null;
      if (remove != null)
        msgs = ((InternalEObject)remove).eInverseRemove(this, EOPPOSITE_FEATURE_BASE - DJPackage.CLASSM__REMOVE, null, msgs);
      if (newRemove != null)
        msgs = ((InternalEObject)newRemove).eInverseAdd(this, EOPPOSITE_FEATURE_BASE - DJPackage.CLASSM__REMOVE, null, msgs);
      msgs = basicSetRemove(newRemove, msgs);
      if (msgs != null) msgs.dispatch();
    }
    else if (eNotificationRequired())
      eNotify(new ENotificationImpl(this, Notification.SET, DJPackage.CLASSM__REMOVE, newRemove, newRemove));
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
      case DJPackage.CLASSM__MODIFIES:
        return basicSetModifies(null, msgs);
      case DJPackage.CLASSM__ADDS:
        return basicSetAdds(null, msgs);
      case DJPackage.CLASSM__REMOVE:
        return basicSetRemove(null, msgs);
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
      case DJPackage.CLASSM__ACTION:
        return getAction();
      case DJPackage.CLASSM__MODIFIES:
        return getModifies();
      case DJPackage.CLASSM__ADDS:
        return getAdds();
      case DJPackage.CLASSM__REMOVE:
        return getRemove();
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
      case DJPackage.CLASSM__ACTION:
        setAction((String)newValue);
        return;
      case DJPackage.CLASSM__MODIFIES:
        setModifies((ModifiesClass)newValue);
        return;
      case DJPackage.CLASSM__ADDS:
        setAdds((AddsClass)newValue);
        return;
      case DJPackage.CLASSM__REMOVE:
        setRemove((RemoveClass)newValue);
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
      case DJPackage.CLASSM__ACTION:
        setAction(ACTION_EDEFAULT);
        return;
      case DJPackage.CLASSM__MODIFIES:
        setModifies((ModifiesClass)null);
        return;
      case DJPackage.CLASSM__ADDS:
        setAdds((AddsClass)null);
        return;
      case DJPackage.CLASSM__REMOVE:
        setRemove((RemoveClass)null);
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
      case DJPackage.CLASSM__ACTION:
        return ACTION_EDEFAULT == null ? action != null : !ACTION_EDEFAULT.equals(action);
      case DJPackage.CLASSM__MODIFIES:
        return modifies != null;
      case DJPackage.CLASSM__ADDS:
        return adds != null;
      case DJPackage.CLASSM__REMOVE:
        return remove != null;
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
    result.append(" (action: ");
    result.append(action);
    result.append(')');
    return result.toString();
  }

} //ClassmImpl
