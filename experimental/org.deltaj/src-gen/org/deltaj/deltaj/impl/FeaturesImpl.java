/**
 * <copyright>
 * </copyright>
 *
 */
package org.deltaj.deltaj.impl;

import java.util.Collection;

import org.deltaj.deltaj.DeltajPackage;
import org.deltaj.deltaj.Feature;
import org.deltaj.deltaj.Features;

import org.eclipse.emf.common.notify.NotificationChain;

import org.eclipse.emf.common.util.EList;

import org.eclipse.emf.ecore.EClass;
import org.eclipse.emf.ecore.InternalEObject;

import org.eclipse.emf.ecore.impl.MinimalEObjectImpl;

import org.eclipse.emf.ecore.util.EObjectContainmentEList;
import org.eclipse.emf.ecore.util.InternalEList;

/**
 * <!-- begin-user-doc -->
 * An implementation of the model object '<em><b>Features</b></em>'.
 * <!-- end-user-doc -->
 * <p>
 * The following features are implemented:
 * <ul>
 *   <li>{@link org.deltaj.deltaj.impl.FeaturesImpl#getFeaturesList <em>Features List</em>}</li>
 * </ul>
 * </p>
 *
 * @generated
 */
public class FeaturesImpl extends MinimalEObjectImpl.Container implements Features
{
  /**
   * The cached value of the '{@link #getFeaturesList() <em>Features List</em>}' containment reference list.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see #getFeaturesList()
   * @generated
   * @ordered
   */
  protected EList<Feature> featuresList;

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  protected FeaturesImpl()
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
    return DeltajPackage.Literals.FEATURES;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public EList<Feature> getFeaturesList()
  {
    if (featuresList == null)
    {
      featuresList = new EObjectContainmentEList<Feature>(Feature.class, this, DeltajPackage.FEATURES__FEATURES_LIST);
    }
    return featuresList;
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
      case DeltajPackage.FEATURES__FEATURES_LIST:
        return ((InternalEList<?>)getFeaturesList()).basicRemove(otherEnd, msgs);
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
      case DeltajPackage.FEATURES__FEATURES_LIST:
        return getFeaturesList();
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
      case DeltajPackage.FEATURES__FEATURES_LIST:
        getFeaturesList().clear();
        getFeaturesList().addAll((Collection<? extends Feature>)newValue);
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
      case DeltajPackage.FEATURES__FEATURES_LIST:
        getFeaturesList().clear();
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
      case DeltajPackage.FEATURES__FEATURES_LIST:
        return featuresList != null && !featuresList.isEmpty();
    }
    return super.eIsSet(featureID);
  }

} //FeaturesImpl
