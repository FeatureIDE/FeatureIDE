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
import org.xtext.example.dJ.Type;

/**
 * <!-- begin-user-doc -->
 * An implementation of the model object '<em><b>Type</b></em>'.
 * <!-- end-user-doc -->
 * <p>
 * The following features are implemented:
 * <ul>
 *   <li>{@link org.xtext.example.dJ.impl.TypeImpl#getBasic <em>Basic</em>}</li>
 *   <li>{@link org.xtext.example.dJ.impl.TypeImpl#getClassref <em>Classref</em>}</li>
 * </ul>
 * </p>
 *
 * @generated
 */
public class TypeImpl extends MinimalEObjectImpl.Container implements Type
{
  /**
   * The default value of the '{@link #getBasic() <em>Basic</em>}' attribute.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see #getBasic()
   * @generated
   * @ordered
   */
  protected static final String BASIC_EDEFAULT = null;

  /**
   * The cached value of the '{@link #getBasic() <em>Basic</em>}' attribute.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see #getBasic()
   * @generated
   * @ordered
   */
  protected String basic = BASIC_EDEFAULT;

  /**
   * The cached value of the '{@link #getClassref() <em>Classref</em>}' reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see #getClassref()
   * @generated
   * @ordered
   */
  protected org.xtext.example.dJ.Class classref;

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  protected TypeImpl()
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
    return DJPackage.Literals.TYPE;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public String getBasic()
  {
    return basic;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public void setBasic(String newBasic)
  {
    String oldBasic = basic;
    basic = newBasic;
    if (eNotificationRequired())
      eNotify(new ENotificationImpl(this, Notification.SET, DJPackage.TYPE__BASIC, oldBasic, basic));
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public org.xtext.example.dJ.Class getClassref()
  {
    if (classref != null && classref.eIsProxy())
    {
      InternalEObject oldClassref = (InternalEObject)classref;
      classref = (org.xtext.example.dJ.Class)eResolveProxy(oldClassref);
      if (classref != oldClassref)
      {
        if (eNotificationRequired())
          eNotify(new ENotificationImpl(this, Notification.RESOLVE, DJPackage.TYPE__CLASSREF, oldClassref, classref));
      }
    }
    return classref;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public org.xtext.example.dJ.Class basicGetClassref()
  {
    return classref;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public void setClassref(org.xtext.example.dJ.Class newClassref)
  {
    org.xtext.example.dJ.Class oldClassref = classref;
    classref = newClassref;
    if (eNotificationRequired())
      eNotify(new ENotificationImpl(this, Notification.SET, DJPackage.TYPE__CLASSREF, oldClassref, classref));
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
      case DJPackage.TYPE__BASIC:
        return getBasic();
      case DJPackage.TYPE__CLASSREF:
        if (resolve) return getClassref();
        return basicGetClassref();
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
      case DJPackage.TYPE__BASIC:
        setBasic((String)newValue);
        return;
      case DJPackage.TYPE__CLASSREF:
        setClassref((org.xtext.example.dJ.Class)newValue);
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
      case DJPackage.TYPE__BASIC:
        setBasic(BASIC_EDEFAULT);
        return;
      case DJPackage.TYPE__CLASSREF:
        setClassref((org.xtext.example.dJ.Class)null);
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
      case DJPackage.TYPE__BASIC:
        return BASIC_EDEFAULT == null ? basic != null : !BASIC_EDEFAULT.equals(basic);
      case DJPackage.TYPE__CLASSREF:
        return classref != null;
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
    result.append(" (basic: ");
    result.append(basic);
    result.append(')');
    return result.toString();
  }

} //TypeImpl
