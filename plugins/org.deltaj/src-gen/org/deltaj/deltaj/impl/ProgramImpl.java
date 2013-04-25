/**
 * <copyright>
 * </copyright>
 *
 */
package org.deltaj.deltaj.impl;

import java.util.Collection;

import org.deltaj.deltaj.DeltaModule;
import org.deltaj.deltaj.DeltajPackage;
import org.deltaj.deltaj.Product;
import org.deltaj.deltaj.ProductLine;
import org.deltaj.deltaj.Program;

import org.eclipse.emf.common.notify.NotificationChain;

import org.eclipse.emf.common.util.EList;

import org.eclipse.emf.ecore.EClass;
import org.eclipse.emf.ecore.InternalEObject;

import org.eclipse.emf.ecore.impl.MinimalEObjectImpl;

import org.eclipse.emf.ecore.util.EObjectContainmentEList;
import org.eclipse.emf.ecore.util.InternalEList;

/**
 * <!-- begin-user-doc -->
 * An implementation of the model object '<em><b>Program</b></em>'.
 * <!-- end-user-doc -->
 * <p>
 * The following features are implemented:
 * <ul>
 *   <li>{@link org.deltaj.deltaj.impl.ProgramImpl#getDeltaModules <em>Delta Modules</em>}</li>
 *   <li>{@link org.deltaj.deltaj.impl.ProgramImpl#getProductLines <em>Product Lines</em>}</li>
 *   <li>{@link org.deltaj.deltaj.impl.ProgramImpl#getProducts <em>Products</em>}</li>
 * </ul>
 * </p>
 *
 * @generated
 */
public class ProgramImpl extends MinimalEObjectImpl.Container implements Program
{
  /**
   * The cached value of the '{@link #getDeltaModules() <em>Delta Modules</em>}' containment reference list.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see #getDeltaModules()
   * @generated
   * @ordered
   */
  protected EList<DeltaModule> deltaModules;

  /**
   * The cached value of the '{@link #getProductLines() <em>Product Lines</em>}' containment reference list.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see #getProductLines()
   * @generated
   * @ordered
   */
  protected EList<ProductLine> productLines;

  /**
   * The cached value of the '{@link #getProducts() <em>Products</em>}' containment reference list.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see #getProducts()
   * @generated
   * @ordered
   */
  protected EList<Product> products;

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  protected ProgramImpl()
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
    return DeltajPackage.Literals.PROGRAM;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public EList<DeltaModule> getDeltaModules()
  {
    if (deltaModules == null)
    {
      deltaModules = new EObjectContainmentEList<DeltaModule>(DeltaModule.class, this, DeltajPackage.PROGRAM__DELTA_MODULES);
    }
    return deltaModules;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public EList<ProductLine> getProductLines()
  {
    if (productLines == null)
    {
      productLines = new EObjectContainmentEList<ProductLine>(ProductLine.class, this, DeltajPackage.PROGRAM__PRODUCT_LINES);
    }
    return productLines;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public EList<Product> getProducts()
  {
    if (products == null)
    {
      products = new EObjectContainmentEList<Product>(Product.class, this, DeltajPackage.PROGRAM__PRODUCTS);
    }
    return products;
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
      case DeltajPackage.PROGRAM__DELTA_MODULES:
        return ((InternalEList<?>)getDeltaModules()).basicRemove(otherEnd, msgs);
      case DeltajPackage.PROGRAM__PRODUCT_LINES:
        return ((InternalEList<?>)getProductLines()).basicRemove(otherEnd, msgs);
      case DeltajPackage.PROGRAM__PRODUCTS:
        return ((InternalEList<?>)getProducts()).basicRemove(otherEnd, msgs);
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
      case DeltajPackage.PROGRAM__DELTA_MODULES:
        return getDeltaModules();
      case DeltajPackage.PROGRAM__PRODUCT_LINES:
        return getProductLines();
      case DeltajPackage.PROGRAM__PRODUCTS:
        return getProducts();
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
      case DeltajPackage.PROGRAM__DELTA_MODULES:
        getDeltaModules().clear();
        getDeltaModules().addAll((Collection<? extends DeltaModule>)newValue);
        return;
      case DeltajPackage.PROGRAM__PRODUCT_LINES:
        getProductLines().clear();
        getProductLines().addAll((Collection<? extends ProductLine>)newValue);
        return;
      case DeltajPackage.PROGRAM__PRODUCTS:
        getProducts().clear();
        getProducts().addAll((Collection<? extends Product>)newValue);
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
      case DeltajPackage.PROGRAM__DELTA_MODULES:
        getDeltaModules().clear();
        return;
      case DeltajPackage.PROGRAM__PRODUCT_LINES:
        getProductLines().clear();
        return;
      case DeltajPackage.PROGRAM__PRODUCTS:
        getProducts().clear();
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
      case DeltajPackage.PROGRAM__DELTA_MODULES:
        return deltaModules != null && !deltaModules.isEmpty();
      case DeltajPackage.PROGRAM__PRODUCT_LINES:
        return productLines != null && !productLines.isEmpty();
      case DeltajPackage.PROGRAM__PRODUCTS:
        return products != null && !products.isEmpty();
    }
    return super.eIsSet(featureID);
  }

} //ProgramImpl
