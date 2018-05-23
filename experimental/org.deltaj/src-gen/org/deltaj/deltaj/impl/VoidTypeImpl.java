/**
 * <copyright>
 * </copyright>
 *
 */
package org.deltaj.deltaj.impl;

import org.deltaj.deltaj.DeltajPackage;
import org.deltaj.deltaj.VoidType;

import org.eclipse.emf.common.notify.Notification;

import org.eclipse.emf.ecore.EClass;

import org.eclipse.emf.ecore.impl.ENotificationImpl;

/**
 * <!-- begin-user-doc -->
 * An implementation of the model object '<em><b>Void Type</b></em>'.
 * <!-- end-user-doc -->
 * <p>
 * The following features are implemented:
 * <ul>
 *   <li>{@link org.deltaj.deltaj.impl.VoidTypeImpl#getVoid <em>Void</em>}</li>
 * </ul>
 * </p>
 *
 * @generated
 */
public class VoidTypeImpl extends TypeForMethodImpl implements VoidType
{
  /**
   * The default value of the '{@link #getVoid() <em>Void</em>}' attribute.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see #getVoid()
   * @generated
   * @ordered
   */
  protected static final String VOID_EDEFAULT = null;

  /**
   * The cached value of the '{@link #getVoid() <em>Void</em>}' attribute.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see #getVoid()
   * @generated
   * @ordered
   */
  protected String void_ = VOID_EDEFAULT;

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  protected VoidTypeImpl()
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
    return DeltajPackage.Literals.VOID_TYPE;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public String getVoid()
  {
    return void_;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public void setVoid(String newVoid)
  {
    String oldVoid = void_;
    void_ = newVoid;
    if (eNotificationRequired())
      eNotify(new ENotificationImpl(this, Notification.SET, DeltajPackage.VOID_TYPE__VOID, oldVoid, void_));
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
      case DeltajPackage.VOID_TYPE__VOID:
        return getVoid();
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
      case DeltajPackage.VOID_TYPE__VOID:
        setVoid((String)newValue);
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
      case DeltajPackage.VOID_TYPE__VOID:
        setVoid(VOID_EDEFAULT);
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
      case DeltajPackage.VOID_TYPE__VOID:
        return VOID_EDEFAULT == null ? void_ != null : !VOID_EDEFAULT.equals(void_);
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
    result.append(" (void: ");
    result.append(void_);
    result.append(')');
    return result.toString();
  }

} //VoidTypeImpl
