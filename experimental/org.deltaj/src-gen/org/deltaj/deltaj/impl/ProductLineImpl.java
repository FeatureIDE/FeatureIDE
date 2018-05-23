/**
 * <copyright>
 * </copyright>
 *
 */
package org.deltaj.deltaj.impl;

import org.deltaj.deltaj.Configurations;
import org.deltaj.deltaj.DeltaPartition;
import org.deltaj.deltaj.DeltajPackage;
import org.deltaj.deltaj.Features;
import org.deltaj.deltaj.ProductLine;

import org.eclipse.emf.common.notify.Notification;
import org.eclipse.emf.common.notify.NotificationChain;

import org.eclipse.emf.ecore.EClass;
import org.eclipse.emf.ecore.InternalEObject;

import org.eclipse.emf.ecore.impl.ENotificationImpl;
import org.eclipse.emf.ecore.impl.MinimalEObjectImpl;

/**
 * <!-- begin-user-doc -->
 * An implementation of the model object '<em><b>Product Line</b></em>'.
 * <!-- end-user-doc -->
 * <p>
 * The following features are implemented:
 * <ul>
 *   <li>{@link org.deltaj.deltaj.impl.ProductLineImpl#getName <em>Name</em>}</li>
 *   <li>{@link org.deltaj.deltaj.impl.ProductLineImpl#getFeatures <em>Features</em>}</li>
 *   <li>{@link org.deltaj.deltaj.impl.ProductLineImpl#getConfigurations <em>Configurations</em>}</li>
 *   <li>{@link org.deltaj.deltaj.impl.ProductLineImpl#getPartition <em>Partition</em>}</li>
 * </ul>
 * </p>
 *
 * @generated
 */
public class ProductLineImpl extends MinimalEObjectImpl.Container implements ProductLine
{
  /**
   * The default value of the '{@link #getName() <em>Name</em>}' attribute.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see #getName()
   * @generated
   * @ordered
   */
  protected static final String NAME_EDEFAULT = null;

  /**
   * The cached value of the '{@link #getName() <em>Name</em>}' attribute.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see #getName()
   * @generated
   * @ordered
   */
  protected String name = NAME_EDEFAULT;

  /**
   * The cached value of the '{@link #getFeatures() <em>Features</em>}' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see #getFeatures()
   * @generated
   * @ordered
   */
  protected Features features;

  /**
   * The cached value of the '{@link #getConfigurations() <em>Configurations</em>}' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see #getConfigurations()
   * @generated
   * @ordered
   */
  protected Configurations configurations;

  /**
   * The cached value of the '{@link #getPartition() <em>Partition</em>}' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see #getPartition()
   * @generated
   * @ordered
   */
  protected DeltaPartition partition;

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  protected ProductLineImpl()
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
    return DeltajPackage.Literals.PRODUCT_LINE;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public String getName()
  {
    return name;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public void setName(String newName)
  {
    String oldName = name;
    name = newName;
    if (eNotificationRequired())
      eNotify(new ENotificationImpl(this, Notification.SET, DeltajPackage.PRODUCT_LINE__NAME, oldName, name));
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public Features getFeatures()
  {
    return features;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public NotificationChain basicSetFeatures(Features newFeatures, NotificationChain msgs)
  {
    Features oldFeatures = features;
    features = newFeatures;
    if (eNotificationRequired())
    {
      ENotificationImpl notification = new ENotificationImpl(this, Notification.SET, DeltajPackage.PRODUCT_LINE__FEATURES, oldFeatures, newFeatures);
      if (msgs == null) msgs = notification; else msgs.add(notification);
    }
    return msgs;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public void setFeatures(Features newFeatures)
  {
    if (newFeatures != features)
    {
      NotificationChain msgs = null;
      if (features != null)
        msgs = ((InternalEObject)features).eInverseRemove(this, EOPPOSITE_FEATURE_BASE - DeltajPackage.PRODUCT_LINE__FEATURES, null, msgs);
      if (newFeatures != null)
        msgs = ((InternalEObject)newFeatures).eInverseAdd(this, EOPPOSITE_FEATURE_BASE - DeltajPackage.PRODUCT_LINE__FEATURES, null, msgs);
      msgs = basicSetFeatures(newFeatures, msgs);
      if (msgs != null) msgs.dispatch();
    }
    else if (eNotificationRequired())
      eNotify(new ENotificationImpl(this, Notification.SET, DeltajPackage.PRODUCT_LINE__FEATURES, newFeatures, newFeatures));
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public Configurations getConfigurations()
  {
    return configurations;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public NotificationChain basicSetConfigurations(Configurations newConfigurations, NotificationChain msgs)
  {
    Configurations oldConfigurations = configurations;
    configurations = newConfigurations;
    if (eNotificationRequired())
    {
      ENotificationImpl notification = new ENotificationImpl(this, Notification.SET, DeltajPackage.PRODUCT_LINE__CONFIGURATIONS, oldConfigurations, newConfigurations);
      if (msgs == null) msgs = notification; else msgs.add(notification);
    }
    return msgs;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public void setConfigurations(Configurations newConfigurations)
  {
    if (newConfigurations != configurations)
    {
      NotificationChain msgs = null;
      if (configurations != null)
        msgs = ((InternalEObject)configurations).eInverseRemove(this, EOPPOSITE_FEATURE_BASE - DeltajPackage.PRODUCT_LINE__CONFIGURATIONS, null, msgs);
      if (newConfigurations != null)
        msgs = ((InternalEObject)newConfigurations).eInverseAdd(this, EOPPOSITE_FEATURE_BASE - DeltajPackage.PRODUCT_LINE__CONFIGURATIONS, null, msgs);
      msgs = basicSetConfigurations(newConfigurations, msgs);
      if (msgs != null) msgs.dispatch();
    }
    else if (eNotificationRequired())
      eNotify(new ENotificationImpl(this, Notification.SET, DeltajPackage.PRODUCT_LINE__CONFIGURATIONS, newConfigurations, newConfigurations));
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public DeltaPartition getPartition()
  {
    return partition;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public NotificationChain basicSetPartition(DeltaPartition newPartition, NotificationChain msgs)
  {
    DeltaPartition oldPartition = partition;
    partition = newPartition;
    if (eNotificationRequired())
    {
      ENotificationImpl notification = new ENotificationImpl(this, Notification.SET, DeltajPackage.PRODUCT_LINE__PARTITION, oldPartition, newPartition);
      if (msgs == null) msgs = notification; else msgs.add(notification);
    }
    return msgs;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public void setPartition(DeltaPartition newPartition)
  {
    if (newPartition != partition)
    {
      NotificationChain msgs = null;
      if (partition != null)
        msgs = ((InternalEObject)partition).eInverseRemove(this, EOPPOSITE_FEATURE_BASE - DeltajPackage.PRODUCT_LINE__PARTITION, null, msgs);
      if (newPartition != null)
        msgs = ((InternalEObject)newPartition).eInverseAdd(this, EOPPOSITE_FEATURE_BASE - DeltajPackage.PRODUCT_LINE__PARTITION, null, msgs);
      msgs = basicSetPartition(newPartition, msgs);
      if (msgs != null) msgs.dispatch();
    }
    else if (eNotificationRequired())
      eNotify(new ENotificationImpl(this, Notification.SET, DeltajPackage.PRODUCT_LINE__PARTITION, newPartition, newPartition));
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
      case DeltajPackage.PRODUCT_LINE__FEATURES:
        return basicSetFeatures(null, msgs);
      case DeltajPackage.PRODUCT_LINE__CONFIGURATIONS:
        return basicSetConfigurations(null, msgs);
      case DeltajPackage.PRODUCT_LINE__PARTITION:
        return basicSetPartition(null, msgs);
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
      case DeltajPackage.PRODUCT_LINE__NAME:
        return getName();
      case DeltajPackage.PRODUCT_LINE__FEATURES:
        return getFeatures();
      case DeltajPackage.PRODUCT_LINE__CONFIGURATIONS:
        return getConfigurations();
      case DeltajPackage.PRODUCT_LINE__PARTITION:
        return getPartition();
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
      case DeltajPackage.PRODUCT_LINE__NAME:
        setName((String)newValue);
        return;
      case DeltajPackage.PRODUCT_LINE__FEATURES:
        setFeatures((Features)newValue);
        return;
      case DeltajPackage.PRODUCT_LINE__CONFIGURATIONS:
        setConfigurations((Configurations)newValue);
        return;
      case DeltajPackage.PRODUCT_LINE__PARTITION:
        setPartition((DeltaPartition)newValue);
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
      case DeltajPackage.PRODUCT_LINE__NAME:
        setName(NAME_EDEFAULT);
        return;
      case DeltajPackage.PRODUCT_LINE__FEATURES:
        setFeatures((Features)null);
        return;
      case DeltajPackage.PRODUCT_LINE__CONFIGURATIONS:
        setConfigurations((Configurations)null);
        return;
      case DeltajPackage.PRODUCT_LINE__PARTITION:
        setPartition((DeltaPartition)null);
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
      case DeltajPackage.PRODUCT_LINE__NAME:
        return NAME_EDEFAULT == null ? name != null : !NAME_EDEFAULT.equals(name);
      case DeltajPackage.PRODUCT_LINE__FEATURES:
        return features != null;
      case DeltajPackage.PRODUCT_LINE__CONFIGURATIONS:
        return configurations != null;
      case DeltajPackage.PRODUCT_LINE__PARTITION:
        return partition != null;
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
    result.append(" (name: ");
    result.append(name);
    result.append(')');
    return result.toString();
  }

} //ProductLineImpl
