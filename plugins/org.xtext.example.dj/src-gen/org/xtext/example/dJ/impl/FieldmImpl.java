/**
 * <copyright>
 * </copyright>
 *
 */
package org.xtext.example.dJ.impl;

import java.util.Collection;

import org.eclipse.emf.common.notify.NotificationChain;

import org.eclipse.emf.common.util.EList;

import org.eclipse.emf.ecore.EClass;
import org.eclipse.emf.ecore.InternalEObject;

import org.eclipse.emf.ecore.impl.MinimalEObjectImpl;

import org.eclipse.emf.ecore.util.EObjectContainmentEList;
import org.eclipse.emf.ecore.util.InternalEList;

import org.xtext.example.dJ.AddsField;
import org.xtext.example.dJ.DJPackage;
import org.xtext.example.dJ.Fieldm;
import org.xtext.example.dJ.RemovesField;

/**
 * <!-- begin-user-doc -->
 * An implementation of the model object '<em><b>Fieldm</b></em>'.
 * <!-- end-user-doc -->
 * <p>
 * The following features are implemented:
 * <ul>
 *   <li>{@link org.xtext.example.dJ.impl.FieldmImpl#getRemoveList <em>Remove List</em>}</li>
 *   <li>{@link org.xtext.example.dJ.impl.FieldmImpl#getAddsList <em>Adds List</em>}</li>
 * </ul>
 * </p>
 *
 * @generated
 */
public class FieldmImpl extends MinimalEObjectImpl.Container implements Fieldm
{
  /**
   * The cached value of the '{@link #getRemoveList() <em>Remove List</em>}' containment reference list.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see #getRemoveList()
   * @generated
   * @ordered
   */
  protected EList<RemovesField> removeList;

  /**
   * The cached value of the '{@link #getAddsList() <em>Adds List</em>}' containment reference list.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see #getAddsList()
   * @generated
   * @ordered
   */
  protected EList<AddsField> addsList;

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  protected FieldmImpl()
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
    return DJPackage.Literals.FIELDM;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public EList<RemovesField> getRemoveList()
  {
    if (removeList == null)
    {
      removeList = new EObjectContainmentEList<RemovesField>(RemovesField.class, this, DJPackage.FIELDM__REMOVE_LIST);
    }
    return removeList;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public EList<AddsField> getAddsList()
  {
    if (addsList == null)
    {
      addsList = new EObjectContainmentEList<AddsField>(AddsField.class, this, DJPackage.FIELDM__ADDS_LIST);
    }
    return addsList;
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
      case DJPackage.FIELDM__REMOVE_LIST:
        return ((InternalEList<?>)getRemoveList()).basicRemove(otherEnd, msgs);
      case DJPackage.FIELDM__ADDS_LIST:
        return ((InternalEList<?>)getAddsList()).basicRemove(otherEnd, msgs);
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
      case DJPackage.FIELDM__REMOVE_LIST:
        return getRemoveList();
      case DJPackage.FIELDM__ADDS_LIST:
        return getAddsList();
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
      case DJPackage.FIELDM__REMOVE_LIST:
        getRemoveList().clear();
        getRemoveList().addAll((Collection<? extends RemovesField>)newValue);
        return;
      case DJPackage.FIELDM__ADDS_LIST:
        getAddsList().clear();
        getAddsList().addAll((Collection<? extends AddsField>)newValue);
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
      case DJPackage.FIELDM__REMOVE_LIST:
        getRemoveList().clear();
        return;
      case DJPackage.FIELDM__ADDS_LIST:
        getAddsList().clear();
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
      case DJPackage.FIELDM__REMOVE_LIST:
        return removeList != null && !removeList.isEmpty();
      case DJPackage.FIELDM__ADDS_LIST:
        return addsList != null && !addsList.isEmpty();
    }
    return super.eIsSet(featureID);
  }

} //FieldmImpl
