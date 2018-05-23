/**
 * <copyright>
 * </copyright>
 *
 */
package org.deltaj.deltaj.impl;

import java.util.Collection;

import org.deltaj.deltaj.ClassModification;
import org.deltaj.deltaj.DeltaSubAction;
import org.deltaj.deltaj.DeltajPackage;

import org.eclipse.emf.common.notify.Notification;
import org.eclipse.emf.common.notify.NotificationChain;

import org.eclipse.emf.common.util.EList;

import org.eclipse.emf.ecore.EClass;
import org.eclipse.emf.ecore.InternalEObject;

import org.eclipse.emf.ecore.impl.ENotificationImpl;

import org.eclipse.emf.ecore.util.EObjectContainmentEList;
import org.eclipse.emf.ecore.util.InternalEList;

/**
 * <!-- begin-user-doc -->
 * An implementation of the model object '<em><b>Class Modification</b></em>'.
 * <!-- end-user-doc -->
 * <p>
 * The following features are implemented:
 * <ul>
 *   <li>{@link org.deltaj.deltaj.impl.ClassModificationImpl#getExtends <em>Extends</em>}</li>
 *   <li>{@link org.deltaj.deltaj.impl.ClassModificationImpl#getSubActions <em>Sub Actions</em>}</li>
 * </ul>
 * </p>
 *
 * @generated
 */
public class ClassModificationImpl extends RemovesOrModifiesClassImpl implements ClassModification
{
  /**
   * The default value of the '{@link #getExtends() <em>Extends</em>}' attribute.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see #getExtends()
   * @generated
   * @ordered
   */
  protected static final String EXTENDS_EDEFAULT = null;

  /**
   * The cached value of the '{@link #getExtends() <em>Extends</em>}' attribute.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see #getExtends()
   * @generated
   * @ordered
   */
  protected String extends_ = EXTENDS_EDEFAULT;

  /**
   * The cached value of the '{@link #getSubActions() <em>Sub Actions</em>}' containment reference list.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see #getSubActions()
   * @generated
   * @ordered
   */
  protected EList<DeltaSubAction> subActions;

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  protected ClassModificationImpl()
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
    return DeltajPackage.Literals.CLASS_MODIFICATION;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public String getExtends()
  {
    return extends_;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public void setExtends(String newExtends)
  {
    String oldExtends = extends_;
    extends_ = newExtends;
    if (eNotificationRequired())
      eNotify(new ENotificationImpl(this, Notification.SET, DeltajPackage.CLASS_MODIFICATION__EXTENDS, oldExtends, extends_));
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public EList<DeltaSubAction> getSubActions()
  {
    if (subActions == null)
    {
      subActions = new EObjectContainmentEList<DeltaSubAction>(DeltaSubAction.class, this, DeltajPackage.CLASS_MODIFICATION__SUB_ACTIONS);
    }
    return subActions;
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
      case DeltajPackage.CLASS_MODIFICATION__SUB_ACTIONS:
        return ((InternalEList<?>)getSubActions()).basicRemove(otherEnd, msgs);
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
      case DeltajPackage.CLASS_MODIFICATION__EXTENDS:
        return getExtends();
      case DeltajPackage.CLASS_MODIFICATION__SUB_ACTIONS:
        return getSubActions();
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
      case DeltajPackage.CLASS_MODIFICATION__EXTENDS:
        setExtends((String)newValue);
        return;
      case DeltajPackage.CLASS_MODIFICATION__SUB_ACTIONS:
        getSubActions().clear();
        getSubActions().addAll((Collection<? extends DeltaSubAction>)newValue);
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
      case DeltajPackage.CLASS_MODIFICATION__EXTENDS:
        setExtends(EXTENDS_EDEFAULT);
        return;
      case DeltajPackage.CLASS_MODIFICATION__SUB_ACTIONS:
        getSubActions().clear();
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
      case DeltajPackage.CLASS_MODIFICATION__EXTENDS:
        return EXTENDS_EDEFAULT == null ? extends_ != null : !EXTENDS_EDEFAULT.equals(extends_);
      case DeltajPackage.CLASS_MODIFICATION__SUB_ACTIONS:
        return subActions != null && !subActions.isEmpty();
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
    result.append(" (extends: ");
    result.append(extends_);
    result.append(')');
    return result.toString();
  }

} //ClassModificationImpl
