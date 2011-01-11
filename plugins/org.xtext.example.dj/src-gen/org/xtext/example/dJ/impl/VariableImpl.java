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
import org.xtext.example.dJ.FieldRef;
import org.xtext.example.dJ.Parameter;
import org.xtext.example.dJ.Variable;

/**
 * <!-- begin-user-doc -->
 * An implementation of the model object '<em><b>Variable</b></em>'.
 * <!-- end-user-doc -->
 * <p>
 * The following features are implemented:
 * <ul>
 *   <li>{@link org.xtext.example.dJ.impl.VariableImpl#getParameter <em>Parameter</em>}</li>
 *   <li>{@link org.xtext.example.dJ.impl.VariableImpl#getFieldRef <em>Field Ref</em>}</li>
 * </ul>
 * </p>
 *
 * @generated
 */
public class VariableImpl extends MinimalEObjectImpl.Container implements Variable
{
  /**
   * The cached value of the '{@link #getParameter() <em>Parameter</em>}' reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see #getParameter()
   * @generated
   * @ordered
   */
  protected Parameter parameter;

  /**
   * The cached value of the '{@link #getFieldRef() <em>Field Ref</em>}' reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see #getFieldRef()
   * @generated
   * @ordered
   */
  protected FieldRef fieldRef;

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  protected VariableImpl()
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
    return DJPackage.Literals.VARIABLE;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public Parameter getParameter()
  {
    if (parameter != null && parameter.eIsProxy())
    {
      InternalEObject oldParameter = (InternalEObject)parameter;
      parameter = (Parameter)eResolveProxy(oldParameter);
      if (parameter != oldParameter)
      {
        if (eNotificationRequired())
          eNotify(new ENotificationImpl(this, Notification.RESOLVE, DJPackage.VARIABLE__PARAMETER, oldParameter, parameter));
      }
    }
    return parameter;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public Parameter basicGetParameter()
  {
    return parameter;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public void setParameter(Parameter newParameter)
  {
    Parameter oldParameter = parameter;
    parameter = newParameter;
    if (eNotificationRequired())
      eNotify(new ENotificationImpl(this, Notification.SET, DJPackage.VARIABLE__PARAMETER, oldParameter, parameter));
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public FieldRef getFieldRef()
  {
    if (fieldRef != null && fieldRef.eIsProxy())
    {
      InternalEObject oldFieldRef = (InternalEObject)fieldRef;
      fieldRef = (FieldRef)eResolveProxy(oldFieldRef);
      if (fieldRef != oldFieldRef)
      {
        if (eNotificationRequired())
          eNotify(new ENotificationImpl(this, Notification.RESOLVE, DJPackage.VARIABLE__FIELD_REF, oldFieldRef, fieldRef));
      }
    }
    return fieldRef;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public FieldRef basicGetFieldRef()
  {
    return fieldRef;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public void setFieldRef(FieldRef newFieldRef)
  {
    FieldRef oldFieldRef = fieldRef;
    fieldRef = newFieldRef;
    if (eNotificationRequired())
      eNotify(new ENotificationImpl(this, Notification.SET, DJPackage.VARIABLE__FIELD_REF, oldFieldRef, fieldRef));
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
      case DJPackage.VARIABLE__PARAMETER:
        if (resolve) return getParameter();
        return basicGetParameter();
      case DJPackage.VARIABLE__FIELD_REF:
        if (resolve) return getFieldRef();
        return basicGetFieldRef();
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
      case DJPackage.VARIABLE__PARAMETER:
        setParameter((Parameter)newValue);
        return;
      case DJPackage.VARIABLE__FIELD_REF:
        setFieldRef((FieldRef)newValue);
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
      case DJPackage.VARIABLE__PARAMETER:
        setParameter((Parameter)null);
        return;
      case DJPackage.VARIABLE__FIELD_REF:
        setFieldRef((FieldRef)null);
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
      case DJPackage.VARIABLE__PARAMETER:
        return parameter != null;
      case DJPackage.VARIABLE__FIELD_REF:
        return fieldRef != null;
    }
    return super.eIsSet(featureID);
  }

} //VariableImpl
