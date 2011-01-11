/**
 * <copyright>
 * </copyright>
 *
 */
package org.xtext.example.dJ.impl;

import java.util.Collection;

import org.eclipse.emf.common.notify.Notification;
import org.eclipse.emf.common.notify.NotificationChain;

import org.eclipse.emf.common.util.EList;

import org.eclipse.emf.ecore.EClass;
import org.eclipse.emf.ecore.InternalEObject;

import org.eclipse.emf.ecore.impl.ENotificationImpl;
import org.eclipse.emf.ecore.impl.MinimalEObjectImpl;

import org.eclipse.emf.ecore.util.EObjectContainmentEList;
import org.eclipse.emf.ecore.util.InternalEList;

import org.xtext.example.dJ.DJPackage;
import org.xtext.example.dJ.Features;
import org.xtext.example.dJ.Import;
import org.xtext.example.dJ.Module;
import org.xtext.example.dJ.Program;

/**
 * <!-- begin-user-doc -->
 * An implementation of the model object '<em><b>Program</b></em>'.
 * <!-- end-user-doc -->
 * <p>
 * The following features are implemented:
 * <ul>
 *   <li>{@link org.xtext.example.dJ.impl.ProgramImpl#getImports <em>Imports</em>}</li>
 *   <li>{@link org.xtext.example.dJ.impl.ProgramImpl#getFeatures <em>Features</em>}</li>
 *   <li>{@link org.xtext.example.dJ.impl.ProgramImpl#getModulesList <em>Modules List</em>}</li>
 * </ul>
 * </p>
 *
 * @generated
 */
public class ProgramImpl extends MinimalEObjectImpl.Container implements Program
{
  /**
   * The cached value of the '{@link #getImports() <em>Imports</em>}' containment reference list.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see #getImports()
   * @generated
   * @ordered
   */
  protected EList<Import> imports;

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
   * The cached value of the '{@link #getModulesList() <em>Modules List</em>}' containment reference list.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see #getModulesList()
   * @generated
   * @ordered
   */
  protected EList<Module> modulesList;

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
    return DJPackage.Literals.PROGRAM;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public EList<Import> getImports()
  {
    if (imports == null)
    {
      imports = new EObjectContainmentEList<Import>(Import.class, this, DJPackage.PROGRAM__IMPORTS);
    }
    return imports;
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
      ENotificationImpl notification = new ENotificationImpl(this, Notification.SET, DJPackage.PROGRAM__FEATURES, oldFeatures, newFeatures);
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
        msgs = ((InternalEObject)features).eInverseRemove(this, EOPPOSITE_FEATURE_BASE - DJPackage.PROGRAM__FEATURES, null, msgs);
      if (newFeatures != null)
        msgs = ((InternalEObject)newFeatures).eInverseAdd(this, EOPPOSITE_FEATURE_BASE - DJPackage.PROGRAM__FEATURES, null, msgs);
      msgs = basicSetFeatures(newFeatures, msgs);
      if (msgs != null) msgs.dispatch();
    }
    else if (eNotificationRequired())
      eNotify(new ENotificationImpl(this, Notification.SET, DJPackage.PROGRAM__FEATURES, newFeatures, newFeatures));
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public EList<Module> getModulesList()
  {
    if (modulesList == null)
    {
      modulesList = new EObjectContainmentEList<Module>(Module.class, this, DJPackage.PROGRAM__MODULES_LIST);
    }
    return modulesList;
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
      case DJPackage.PROGRAM__IMPORTS:
        return ((InternalEList<?>)getImports()).basicRemove(otherEnd, msgs);
      case DJPackage.PROGRAM__FEATURES:
        return basicSetFeatures(null, msgs);
      case DJPackage.PROGRAM__MODULES_LIST:
        return ((InternalEList<?>)getModulesList()).basicRemove(otherEnd, msgs);
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
      case DJPackage.PROGRAM__IMPORTS:
        return getImports();
      case DJPackage.PROGRAM__FEATURES:
        return getFeatures();
      case DJPackage.PROGRAM__MODULES_LIST:
        return getModulesList();
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
      case DJPackage.PROGRAM__IMPORTS:
        getImports().clear();
        getImports().addAll((Collection<? extends Import>)newValue);
        return;
      case DJPackage.PROGRAM__FEATURES:
        setFeatures((Features)newValue);
        return;
      case DJPackage.PROGRAM__MODULES_LIST:
        getModulesList().clear();
        getModulesList().addAll((Collection<? extends Module>)newValue);
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
      case DJPackage.PROGRAM__IMPORTS:
        getImports().clear();
        return;
      case DJPackage.PROGRAM__FEATURES:
        setFeatures((Features)null);
        return;
      case DJPackage.PROGRAM__MODULES_LIST:
        getModulesList().clear();
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
      case DJPackage.PROGRAM__IMPORTS:
        return imports != null && !imports.isEmpty();
      case DJPackage.PROGRAM__FEATURES:
        return features != null;
      case DJPackage.PROGRAM__MODULES_LIST:
        return modulesList != null && !modulesList.isEmpty();
    }
    return super.eIsSet(featureID);
  }

} //ProgramImpl
