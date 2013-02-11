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
import org.eclipse.emf.ecore.util.EObjectResolvingEList;
import org.eclipse.emf.ecore.util.InternalEList;

import org.xtext.example.dJ.Core;
import org.xtext.example.dJ.DJPackage;
import org.xtext.example.dJ.Feature;

/**
 * <!-- begin-user-doc -->
 * An implementation of the model object '<em><b>Core</b></em>'.
 * <!-- end-user-doc -->
 * <p>
 * The following features are implemented:
 * <ul>
 *   <li>{@link org.xtext.example.dJ.impl.CoreImpl#getName <em>Name</em>}</li>
 *   <li>{@link org.xtext.example.dJ.impl.CoreImpl#getClassesList <em>Classes List</em>}</li>
 * </ul>
 * </p>
 *
 * @generated
 */
public class CoreImpl extends MinimalEObjectImpl.Container implements Core
{
  /**
   * The cached value of the '{@link #getName() <em>Name</em>}' reference list.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see #getName()
   * @generated
   * @ordered
   */
  protected EList<Feature> name;

  /**
   * The cached value of the '{@link #getClassesList() <em>Classes List</em>}' containment reference list.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see #getClassesList()
   * @generated
   * @ordered
   */
  protected EList<org.xtext.example.dJ.Class> classesList;

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  protected CoreImpl()
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
    return DJPackage.Literals.CORE;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public EList<Feature> getName()
  {
    if (name == null)
    {
      name = new EObjectResolvingEList<Feature>(Feature.class, this, DJPackage.CORE__NAME);
    }
    return name;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public EList<org.xtext.example.dJ.Class> getClassesList()
  {
    if (classesList == null)
    {
      classesList = new EObjectContainmentEList<org.xtext.example.dJ.Class>(org.xtext.example.dJ.Class.class, this, DJPackage.CORE__CLASSES_LIST);
    }
    return classesList;
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
      case DJPackage.CORE__CLASSES_LIST:
        return ((InternalEList<?>)getClassesList()).basicRemove(otherEnd, msgs);
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
      case DJPackage.CORE__NAME:
        return getName();
      case DJPackage.CORE__CLASSES_LIST:
        return getClassesList();
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
      case DJPackage.CORE__NAME:
        getName().clear();
        getName().addAll((Collection<? extends Feature>)newValue);
        return;
      case DJPackage.CORE__CLASSES_LIST:
        getClassesList().clear();
        getClassesList().addAll((Collection<? extends org.xtext.example.dJ.Class>)newValue);
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
      case DJPackage.CORE__NAME:
        getName().clear();
        return;
      case DJPackage.CORE__CLASSES_LIST:
        getClassesList().clear();
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
      case DJPackage.CORE__NAME:
        return name != null && !name.isEmpty();
      case DJPackage.CORE__CLASSES_LIST:
        return classesList != null && !classesList.isEmpty();
    }
    return super.eIsSet(featureID);
  }

} //CoreImpl
