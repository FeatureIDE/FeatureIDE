/**
 * <copyright>
 * </copyright>
 *
 */
package org.deltaj.deltaj.impl;

import java.util.Collection;

import org.deltaj.deltaj.DeltajPackage;
import org.deltaj.deltaj.ModuleReference;
import org.deltaj.deltaj.PartitionPart;

import org.eclipse.emf.common.notify.NotificationChain;

import org.eclipse.emf.common.util.EList;

import org.eclipse.emf.ecore.EClass;
import org.eclipse.emf.ecore.InternalEObject;

import org.eclipse.emf.ecore.impl.MinimalEObjectImpl;

import org.eclipse.emf.ecore.util.EObjectContainmentEList;
import org.eclipse.emf.ecore.util.InternalEList;

/**
 * <!-- begin-user-doc -->
 * An implementation of the model object '<em><b>Partition Part</b></em>'.
 * <!-- end-user-doc -->
 * <p>
 * The following features are implemented:
 * <ul>
 *   <li>{@link org.deltaj.deltaj.impl.PartitionPartImpl#getModuleReferences <em>Module References</em>}</li>
 * </ul>
 * </p>
 *
 * @generated
 */
public class PartitionPartImpl extends MinimalEObjectImpl.Container implements PartitionPart
{
  /**
   * The cached value of the '{@link #getModuleReferences() <em>Module References</em>}' containment reference list.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see #getModuleReferences()
   * @generated
   * @ordered
   */
  protected EList<ModuleReference> moduleReferences;

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  protected PartitionPartImpl()
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
    return DeltajPackage.Literals.PARTITION_PART;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public EList<ModuleReference> getModuleReferences()
  {
    if (moduleReferences == null)
    {
      moduleReferences = new EObjectContainmentEList<ModuleReference>(ModuleReference.class, this, DeltajPackage.PARTITION_PART__MODULE_REFERENCES);
    }
    return moduleReferences;
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
      case DeltajPackage.PARTITION_PART__MODULE_REFERENCES:
        return ((InternalEList<?>)getModuleReferences()).basicRemove(otherEnd, msgs);
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
      case DeltajPackage.PARTITION_PART__MODULE_REFERENCES:
        return getModuleReferences();
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
      case DeltajPackage.PARTITION_PART__MODULE_REFERENCES:
        getModuleReferences().clear();
        getModuleReferences().addAll((Collection<? extends ModuleReference>)newValue);
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
      case DeltajPackage.PARTITION_PART__MODULE_REFERENCES:
        getModuleReferences().clear();
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
      case DeltajPackage.PARTITION_PART__MODULE_REFERENCES:
        return moduleReferences != null && !moduleReferences.isEmpty();
    }
    return super.eIsSet(featureID);
  }

} //PartitionPartImpl
