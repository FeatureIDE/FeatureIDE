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

import org.xtext.example.dJ.Condition;
import org.xtext.example.dJ.DJPackage;
import org.xtext.example.dJ.Feature;

/**
 * <!-- begin-user-doc -->
 * An implementation of the model object '<em><b>Condition</b></em>'.
 * <!-- end-user-doc -->
 * <p>
 * The following features are implemented:
 * <ul>
 *   <li>{@link org.xtext.example.dJ.impl.ConditionImpl#getComplement <em>Complement</em>}</li>
 *   <li>{@link org.xtext.example.dJ.impl.ConditionImpl#getCondition1 <em>Condition1</em>}</li>
 *   <li>{@link org.xtext.example.dJ.impl.ConditionImpl#getOperation <em>Operation</em>}</li>
 *   <li>{@link org.xtext.example.dJ.impl.ConditionImpl#getCondition2 <em>Condition2</em>}</li>
 *   <li>{@link org.xtext.example.dJ.impl.ConditionImpl#getFeature <em>Feature</em>}</li>
 * </ul>
 * </p>
 *
 * @generated
 */
public class ConditionImpl extends MinimalEObjectImpl.Container implements Condition
{
  /**
   * The default value of the '{@link #getComplement() <em>Complement</em>}' attribute.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see #getComplement()
   * @generated
   * @ordered
   */
  protected static final String COMPLEMENT_EDEFAULT = null;

  /**
   * The cached value of the '{@link #getComplement() <em>Complement</em>}' attribute.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see #getComplement()
   * @generated
   * @ordered
   */
  protected String complement = COMPLEMENT_EDEFAULT;

  /**
   * The cached value of the '{@link #getCondition1() <em>Condition1</em>}' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see #getCondition1()
   * @generated
   * @ordered
   */
  protected Condition condition1;

  /**
   * The default value of the '{@link #getOperation() <em>Operation</em>}' attribute.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see #getOperation()
   * @generated
   * @ordered
   */
  protected static final String OPERATION_EDEFAULT = null;

  /**
   * The cached value of the '{@link #getOperation() <em>Operation</em>}' attribute.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see #getOperation()
   * @generated
   * @ordered
   */
  protected String operation = OPERATION_EDEFAULT;

  /**
   * The cached value of the '{@link #getCondition2() <em>Condition2</em>}' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see #getCondition2()
   * @generated
   * @ordered
   */
  protected Condition condition2;

  /**
   * The cached value of the '{@link #getFeature() <em>Feature</em>}' reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see #getFeature()
   * @generated
   * @ordered
   */
  protected Feature feature;

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  protected ConditionImpl()
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
    return DJPackage.Literals.CONDITION;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public String getComplement()
  {
    return complement;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public void setComplement(String newComplement)
  {
    String oldComplement = complement;
    complement = newComplement;
    if (eNotificationRequired())
      eNotify(new ENotificationImpl(this, Notification.SET, DJPackage.CONDITION__COMPLEMENT, oldComplement, complement));
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public Condition getCondition1()
  {
    return condition1;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public NotificationChain basicSetCondition1(Condition newCondition1, NotificationChain msgs)
  {
    Condition oldCondition1 = condition1;
    condition1 = newCondition1;
    if (eNotificationRequired())
    {
      ENotificationImpl notification = new ENotificationImpl(this, Notification.SET, DJPackage.CONDITION__CONDITION1, oldCondition1, newCondition1);
      if (msgs == null) msgs = notification; else msgs.add(notification);
    }
    return msgs;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public void setCondition1(Condition newCondition1)
  {
    if (newCondition1 != condition1)
    {
      NotificationChain msgs = null;
      if (condition1 != null)
        msgs = ((InternalEObject)condition1).eInverseRemove(this, EOPPOSITE_FEATURE_BASE - DJPackage.CONDITION__CONDITION1, null, msgs);
      if (newCondition1 != null)
        msgs = ((InternalEObject)newCondition1).eInverseAdd(this, EOPPOSITE_FEATURE_BASE - DJPackage.CONDITION__CONDITION1, null, msgs);
      msgs = basicSetCondition1(newCondition1, msgs);
      if (msgs != null) msgs.dispatch();
    }
    else if (eNotificationRequired())
      eNotify(new ENotificationImpl(this, Notification.SET, DJPackage.CONDITION__CONDITION1, newCondition1, newCondition1));
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public String getOperation()
  {
    return operation;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public void setOperation(String newOperation)
  {
    String oldOperation = operation;
    operation = newOperation;
    if (eNotificationRequired())
      eNotify(new ENotificationImpl(this, Notification.SET, DJPackage.CONDITION__OPERATION, oldOperation, operation));
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public Condition getCondition2()
  {
    return condition2;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public NotificationChain basicSetCondition2(Condition newCondition2, NotificationChain msgs)
  {
    Condition oldCondition2 = condition2;
    condition2 = newCondition2;
    if (eNotificationRequired())
    {
      ENotificationImpl notification = new ENotificationImpl(this, Notification.SET, DJPackage.CONDITION__CONDITION2, oldCondition2, newCondition2);
      if (msgs == null) msgs = notification; else msgs.add(notification);
    }
    return msgs;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public void setCondition2(Condition newCondition2)
  {
    if (newCondition2 != condition2)
    {
      NotificationChain msgs = null;
      if (condition2 != null)
        msgs = ((InternalEObject)condition2).eInverseRemove(this, EOPPOSITE_FEATURE_BASE - DJPackage.CONDITION__CONDITION2, null, msgs);
      if (newCondition2 != null)
        msgs = ((InternalEObject)newCondition2).eInverseAdd(this, EOPPOSITE_FEATURE_BASE - DJPackage.CONDITION__CONDITION2, null, msgs);
      msgs = basicSetCondition2(newCondition2, msgs);
      if (msgs != null) msgs.dispatch();
    }
    else if (eNotificationRequired())
      eNotify(new ENotificationImpl(this, Notification.SET, DJPackage.CONDITION__CONDITION2, newCondition2, newCondition2));
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public Feature getFeature()
  {
    if (feature != null && feature.eIsProxy())
    {
      InternalEObject oldFeature = (InternalEObject)feature;
      feature = (Feature)eResolveProxy(oldFeature);
      if (feature != oldFeature)
      {
        if (eNotificationRequired())
          eNotify(new ENotificationImpl(this, Notification.RESOLVE, DJPackage.CONDITION__FEATURE, oldFeature, feature));
      }
    }
    return feature;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public Feature basicGetFeature()
  {
    return feature;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public void setFeature(Feature newFeature)
  {
    Feature oldFeature = feature;
    feature = newFeature;
    if (eNotificationRequired())
      eNotify(new ENotificationImpl(this, Notification.SET, DJPackage.CONDITION__FEATURE, oldFeature, feature));
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
      case DJPackage.CONDITION__CONDITION1:
        return basicSetCondition1(null, msgs);
      case DJPackage.CONDITION__CONDITION2:
        return basicSetCondition2(null, msgs);
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
      case DJPackage.CONDITION__COMPLEMENT:
        return getComplement();
      case DJPackage.CONDITION__CONDITION1:
        return getCondition1();
      case DJPackage.CONDITION__OPERATION:
        return getOperation();
      case DJPackage.CONDITION__CONDITION2:
        return getCondition2();
      case DJPackage.CONDITION__FEATURE:
        if (resolve) return getFeature();
        return basicGetFeature();
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
      case DJPackage.CONDITION__COMPLEMENT:
        setComplement((String)newValue);
        return;
      case DJPackage.CONDITION__CONDITION1:
        setCondition1((Condition)newValue);
        return;
      case DJPackage.CONDITION__OPERATION:
        setOperation((String)newValue);
        return;
      case DJPackage.CONDITION__CONDITION2:
        setCondition2((Condition)newValue);
        return;
      case DJPackage.CONDITION__FEATURE:
        setFeature((Feature)newValue);
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
      case DJPackage.CONDITION__COMPLEMENT:
        setComplement(COMPLEMENT_EDEFAULT);
        return;
      case DJPackage.CONDITION__CONDITION1:
        setCondition1((Condition)null);
        return;
      case DJPackage.CONDITION__OPERATION:
        setOperation(OPERATION_EDEFAULT);
        return;
      case DJPackage.CONDITION__CONDITION2:
        setCondition2((Condition)null);
        return;
      case DJPackage.CONDITION__FEATURE:
        setFeature((Feature)null);
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
      case DJPackage.CONDITION__COMPLEMENT:
        return COMPLEMENT_EDEFAULT == null ? complement != null : !COMPLEMENT_EDEFAULT.equals(complement);
      case DJPackage.CONDITION__CONDITION1:
        return condition1 != null;
      case DJPackage.CONDITION__OPERATION:
        return OPERATION_EDEFAULT == null ? operation != null : !OPERATION_EDEFAULT.equals(operation);
      case DJPackage.CONDITION__CONDITION2:
        return condition2 != null;
      case DJPackage.CONDITION__FEATURE:
        return feature != null;
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
    result.append(" (complement: ");
    result.append(complement);
    result.append(", operation: ");
    result.append(operation);
    result.append(')');
    return result.toString();
  }

} //ConditionImpl
