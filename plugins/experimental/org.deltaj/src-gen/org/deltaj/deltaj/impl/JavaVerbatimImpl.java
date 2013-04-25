/**
 * <copyright>
 * </copyright>
 *
 */
package org.deltaj.deltaj.impl;

import org.deltaj.deltaj.DeltajPackage;
import org.deltaj.deltaj.JavaVerbatim;

import org.eclipse.emf.common.notify.Notification;

import org.eclipse.emf.ecore.EClass;

import org.eclipse.emf.ecore.impl.ENotificationImpl;

/**
 * <!-- begin-user-doc -->
 * An implementation of the model object '<em><b>Java Verbatim</b></em>'.
 * <!-- end-user-doc -->
 * <p>
 * The following features are implemented:
 * <ul>
 *   <li>{@link org.deltaj.deltaj.impl.JavaVerbatimImpl#getVerbatim <em>Verbatim</em>}</li>
 * </ul>
 * </p>
 *
 * @generated
 */
public class JavaVerbatimImpl extends StatementImpl implements JavaVerbatim
{
  /**
   * The default value of the '{@link #getVerbatim() <em>Verbatim</em>}' attribute.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see #getVerbatim()
   * @generated
   * @ordered
   */
  protected static final String VERBATIM_EDEFAULT = null;

  /**
   * The cached value of the '{@link #getVerbatim() <em>Verbatim</em>}' attribute.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see #getVerbatim()
   * @generated
   * @ordered
   */
  protected String verbatim = VERBATIM_EDEFAULT;

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  protected JavaVerbatimImpl()
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
    return DeltajPackage.Literals.JAVA_VERBATIM;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public String getVerbatim()
  {
    return verbatim;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public void setVerbatim(String newVerbatim)
  {
    String oldVerbatim = verbatim;
    verbatim = newVerbatim;
    if (eNotificationRequired())
      eNotify(new ENotificationImpl(this, Notification.SET, DeltajPackage.JAVA_VERBATIM__VERBATIM, oldVerbatim, verbatim));
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
      case DeltajPackage.JAVA_VERBATIM__VERBATIM:
        return getVerbatim();
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
      case DeltajPackage.JAVA_VERBATIM__VERBATIM:
        setVerbatim((String)newValue);
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
      case DeltajPackage.JAVA_VERBATIM__VERBATIM:
        setVerbatim(VERBATIM_EDEFAULT);
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
      case DeltajPackage.JAVA_VERBATIM__VERBATIM:
        return VERBATIM_EDEFAULT == null ? verbatim != null : !VERBATIM_EDEFAULT.equals(verbatim);
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
    result.append(" (verbatim: ");
    result.append(verbatim);
    result.append(')');
    return result.toString();
  }

} //JavaVerbatimImpl
