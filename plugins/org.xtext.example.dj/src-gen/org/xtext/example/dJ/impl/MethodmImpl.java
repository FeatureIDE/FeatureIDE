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

import org.xtext.example.dJ.AddsMethod;
import org.xtext.example.dJ.DJPackage;
import org.xtext.example.dJ.Methodm;
import org.xtext.example.dJ.ModifiesMethod;
import org.xtext.example.dJ.RemovesMethod;

/**
 * <!-- begin-user-doc -->
 * An implementation of the model object '<em><b>Methodm</b></em>'.
 * <!-- end-user-doc -->
 * <p>
 * The following features are implemented:
 * <ul>
 *   <li>{@link org.xtext.example.dJ.impl.MethodmImpl#getRemoveList <em>Remove List</em>}</li>
 *   <li>{@link org.xtext.example.dJ.impl.MethodmImpl#getModifiesList <em>Modifies List</em>}</li>
 *   <li>{@link org.xtext.example.dJ.impl.MethodmImpl#getAddsList <em>Adds List</em>}</li>
 * </ul>
 * </p>
 *
 * @generated
 */
public class MethodmImpl extends MinimalEObjectImpl.Container implements Methodm
{
  /**
   * The cached value of the '{@link #getRemoveList() <em>Remove List</em>}' containment reference list.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see #getRemoveList()
   * @generated
   * @ordered
   */
  protected EList<RemovesMethod> removeList;

  /**
   * The cached value of the '{@link #getModifiesList() <em>Modifies List</em>}' containment reference list.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see #getModifiesList()
   * @generated
   * @ordered
   */
  protected EList<ModifiesMethod> modifiesList;

  /**
   * The cached value of the '{@link #getAddsList() <em>Adds List</em>}' containment reference list.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see #getAddsList()
   * @generated
   * @ordered
   */
  protected EList<AddsMethod> addsList;

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  protected MethodmImpl()
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
    return DJPackage.Literals.METHODM;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public EList<RemovesMethod> getRemoveList()
  {
    if (removeList == null)
    {
      removeList = new EObjectContainmentEList<RemovesMethod>(RemovesMethod.class, this, DJPackage.METHODM__REMOVE_LIST);
    }
    return removeList;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public EList<ModifiesMethod> getModifiesList()
  {
    if (modifiesList == null)
    {
      modifiesList = new EObjectContainmentEList<ModifiesMethod>(ModifiesMethod.class, this, DJPackage.METHODM__MODIFIES_LIST);
    }
    return modifiesList;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public EList<AddsMethod> getAddsList()
  {
    if (addsList == null)
    {
      addsList = new EObjectContainmentEList<AddsMethod>(AddsMethod.class, this, DJPackage.METHODM__ADDS_LIST);
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
      case DJPackage.METHODM__REMOVE_LIST:
        return ((InternalEList<?>)getRemoveList()).basicRemove(otherEnd, msgs);
      case DJPackage.METHODM__MODIFIES_LIST:
        return ((InternalEList<?>)getModifiesList()).basicRemove(otherEnd, msgs);
      case DJPackage.METHODM__ADDS_LIST:
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
      case DJPackage.METHODM__REMOVE_LIST:
        return getRemoveList();
      case DJPackage.METHODM__MODIFIES_LIST:
        return getModifiesList();
      case DJPackage.METHODM__ADDS_LIST:
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
      case DJPackage.METHODM__REMOVE_LIST:
        getRemoveList().clear();
        getRemoveList().addAll((Collection<? extends RemovesMethod>)newValue);
        return;
      case DJPackage.METHODM__MODIFIES_LIST:
        getModifiesList().clear();
        getModifiesList().addAll((Collection<? extends ModifiesMethod>)newValue);
        return;
      case DJPackage.METHODM__ADDS_LIST:
        getAddsList().clear();
        getAddsList().addAll((Collection<? extends AddsMethod>)newValue);
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
      case DJPackage.METHODM__REMOVE_LIST:
        getRemoveList().clear();
        return;
      case DJPackage.METHODM__MODIFIES_LIST:
        getModifiesList().clear();
        return;
      case DJPackage.METHODM__ADDS_LIST:
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
      case DJPackage.METHODM__REMOVE_LIST:
        return removeList != null && !removeList.isEmpty();
      case DJPackage.METHODM__MODIFIES_LIST:
        return modifiesList != null && !modifiesList.isEmpty();
      case DJPackage.METHODM__ADDS_LIST:
        return addsList != null && !addsList.isEmpty();
    }
    return super.eIsSet(featureID);
  }

} //MethodmImpl
