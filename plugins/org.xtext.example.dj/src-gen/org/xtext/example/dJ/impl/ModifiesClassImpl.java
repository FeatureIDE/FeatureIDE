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

import org.xtext.example.dJ.Constructor;
import org.xtext.example.dJ.DJPackage;
import org.xtext.example.dJ.Fieldm;
import org.xtext.example.dJ.Methodm;
import org.xtext.example.dJ.ModifiesClass;

/**
 * <!-- begin-user-doc -->
 * An implementation of the model object '<em><b>Modifies Class</b></em>'.
 * <!-- end-user-doc -->
 * <p>
 * The following features are implemented:
 * <ul>
 *   <li>{@link org.xtext.example.dJ.impl.ModifiesClassImpl#getClass_ <em>Class</em>}</li>
 *   <li>{@link org.xtext.example.dJ.impl.ModifiesClassImpl#getExtends <em>Extends</em>}</li>
 *   <li>{@link org.xtext.example.dJ.impl.ModifiesClassImpl#getField <em>Field</em>}</li>
 *   <li>{@link org.xtext.example.dJ.impl.ModifiesClassImpl#getConstructor <em>Constructor</em>}</li>
 *   <li>{@link org.xtext.example.dJ.impl.ModifiesClassImpl#getMethod <em>Method</em>}</li>
 * </ul>
 * </p>
 *
 * @generated
 */
public class ModifiesClassImpl extends MinimalEObjectImpl.Container implements ModifiesClass
{
  /**
   * The cached value of the '{@link #getClass_() <em>Class</em>}' reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see #getClass_()
   * @generated
   * @ordered
   */
  protected org.xtext.example.dJ.Class class_;

  /**
   * The cached value of the '{@link #getExtends() <em>Extends</em>}' reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see #getExtends()
   * @generated
   * @ordered
   */
  protected org.xtext.example.dJ.Class extends_;

  /**
   * The cached value of the '{@link #getField() <em>Field</em>}' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see #getField()
   * @generated
   * @ordered
   */
  protected Fieldm field;

  /**
   * The cached value of the '{@link #getConstructor() <em>Constructor</em>}' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see #getConstructor()
   * @generated
   * @ordered
   */
  protected Constructor constructor;

  /**
   * The cached value of the '{@link #getMethod() <em>Method</em>}' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see #getMethod()
   * @generated
   * @ordered
   */
  protected Methodm method;

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  protected ModifiesClassImpl()
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
    return DJPackage.Literals.MODIFIES_CLASS;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public org.xtext.example.dJ.Class getClass_()
  {
    if (class_ != null && class_.eIsProxy())
    {
      InternalEObject oldClass = (InternalEObject)class_;
      class_ = (org.xtext.example.dJ.Class)eResolveProxy(oldClass);
      if (class_ != oldClass)
      {
        if (eNotificationRequired())
          eNotify(new ENotificationImpl(this, Notification.RESOLVE, DJPackage.MODIFIES_CLASS__CLASS, oldClass, class_));
      }
    }
    return class_;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public org.xtext.example.dJ.Class basicGetClass()
  {
    return class_;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public void setClass(org.xtext.example.dJ.Class newClass)
  {
    org.xtext.example.dJ.Class oldClass = class_;
    class_ = newClass;
    if (eNotificationRequired())
      eNotify(new ENotificationImpl(this, Notification.SET, DJPackage.MODIFIES_CLASS__CLASS, oldClass, class_));
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public org.xtext.example.dJ.Class getExtends()
  {
    if (extends_ != null && extends_.eIsProxy())
    {
      InternalEObject oldExtends = (InternalEObject)extends_;
      extends_ = (org.xtext.example.dJ.Class)eResolveProxy(oldExtends);
      if (extends_ != oldExtends)
      {
        if (eNotificationRequired())
          eNotify(new ENotificationImpl(this, Notification.RESOLVE, DJPackage.MODIFIES_CLASS__EXTENDS, oldExtends, extends_));
      }
    }
    return extends_;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public org.xtext.example.dJ.Class basicGetExtends()
  {
    return extends_;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public void setExtends(org.xtext.example.dJ.Class newExtends)
  {
    org.xtext.example.dJ.Class oldExtends = extends_;
    extends_ = newExtends;
    if (eNotificationRequired())
      eNotify(new ENotificationImpl(this, Notification.SET, DJPackage.MODIFIES_CLASS__EXTENDS, oldExtends, extends_));
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public Fieldm getField()
  {
    return field;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public NotificationChain basicSetField(Fieldm newField, NotificationChain msgs)
  {
    Fieldm oldField = field;
    field = newField;
    if (eNotificationRequired())
    {
      ENotificationImpl notification = new ENotificationImpl(this, Notification.SET, DJPackage.MODIFIES_CLASS__FIELD, oldField, newField);
      if (msgs == null) msgs = notification; else msgs.add(notification);
    }
    return msgs;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public void setField(Fieldm newField)
  {
    if (newField != field)
    {
      NotificationChain msgs = null;
      if (field != null)
        msgs = ((InternalEObject)field).eInverseRemove(this, EOPPOSITE_FEATURE_BASE - DJPackage.MODIFIES_CLASS__FIELD, null, msgs);
      if (newField != null)
        msgs = ((InternalEObject)newField).eInverseAdd(this, EOPPOSITE_FEATURE_BASE - DJPackage.MODIFIES_CLASS__FIELD, null, msgs);
      msgs = basicSetField(newField, msgs);
      if (msgs != null) msgs.dispatch();
    }
    else if (eNotificationRequired())
      eNotify(new ENotificationImpl(this, Notification.SET, DJPackage.MODIFIES_CLASS__FIELD, newField, newField));
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public Constructor getConstructor()
  {
    return constructor;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public NotificationChain basicSetConstructor(Constructor newConstructor, NotificationChain msgs)
  {
    Constructor oldConstructor = constructor;
    constructor = newConstructor;
    if (eNotificationRequired())
    {
      ENotificationImpl notification = new ENotificationImpl(this, Notification.SET, DJPackage.MODIFIES_CLASS__CONSTRUCTOR, oldConstructor, newConstructor);
      if (msgs == null) msgs = notification; else msgs.add(notification);
    }
    return msgs;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public void setConstructor(Constructor newConstructor)
  {
    if (newConstructor != constructor)
    {
      NotificationChain msgs = null;
      if (constructor != null)
        msgs = ((InternalEObject)constructor).eInverseRemove(this, EOPPOSITE_FEATURE_BASE - DJPackage.MODIFIES_CLASS__CONSTRUCTOR, null, msgs);
      if (newConstructor != null)
        msgs = ((InternalEObject)newConstructor).eInverseAdd(this, EOPPOSITE_FEATURE_BASE - DJPackage.MODIFIES_CLASS__CONSTRUCTOR, null, msgs);
      msgs = basicSetConstructor(newConstructor, msgs);
      if (msgs != null) msgs.dispatch();
    }
    else if (eNotificationRequired())
      eNotify(new ENotificationImpl(this, Notification.SET, DJPackage.MODIFIES_CLASS__CONSTRUCTOR, newConstructor, newConstructor));
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public Methodm getMethod()
  {
    return method;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public NotificationChain basicSetMethod(Methodm newMethod, NotificationChain msgs)
  {
    Methodm oldMethod = method;
    method = newMethod;
    if (eNotificationRequired())
    {
      ENotificationImpl notification = new ENotificationImpl(this, Notification.SET, DJPackage.MODIFIES_CLASS__METHOD, oldMethod, newMethod);
      if (msgs == null) msgs = notification; else msgs.add(notification);
    }
    return msgs;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public void setMethod(Methodm newMethod)
  {
    if (newMethod != method)
    {
      NotificationChain msgs = null;
      if (method != null)
        msgs = ((InternalEObject)method).eInverseRemove(this, EOPPOSITE_FEATURE_BASE - DJPackage.MODIFIES_CLASS__METHOD, null, msgs);
      if (newMethod != null)
        msgs = ((InternalEObject)newMethod).eInverseAdd(this, EOPPOSITE_FEATURE_BASE - DJPackage.MODIFIES_CLASS__METHOD, null, msgs);
      msgs = basicSetMethod(newMethod, msgs);
      if (msgs != null) msgs.dispatch();
    }
    else if (eNotificationRequired())
      eNotify(new ENotificationImpl(this, Notification.SET, DJPackage.MODIFIES_CLASS__METHOD, newMethod, newMethod));
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
      case DJPackage.MODIFIES_CLASS__FIELD:
        return basicSetField(null, msgs);
      case DJPackage.MODIFIES_CLASS__CONSTRUCTOR:
        return basicSetConstructor(null, msgs);
      case DJPackage.MODIFIES_CLASS__METHOD:
        return basicSetMethod(null, msgs);
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
      case DJPackage.MODIFIES_CLASS__CLASS:
        if (resolve) return getClass_();
        return basicGetClass();
      case DJPackage.MODIFIES_CLASS__EXTENDS:
        if (resolve) return getExtends();
        return basicGetExtends();
      case DJPackage.MODIFIES_CLASS__FIELD:
        return getField();
      case DJPackage.MODIFIES_CLASS__CONSTRUCTOR:
        return getConstructor();
      case DJPackage.MODIFIES_CLASS__METHOD:
        return getMethod();
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
      case DJPackage.MODIFIES_CLASS__CLASS:
        setClass((org.xtext.example.dJ.Class)newValue);
        return;
      case DJPackage.MODIFIES_CLASS__EXTENDS:
        setExtends((org.xtext.example.dJ.Class)newValue);
        return;
      case DJPackage.MODIFIES_CLASS__FIELD:
        setField((Fieldm)newValue);
        return;
      case DJPackage.MODIFIES_CLASS__CONSTRUCTOR:
        setConstructor((Constructor)newValue);
        return;
      case DJPackage.MODIFIES_CLASS__METHOD:
        setMethod((Methodm)newValue);
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
      case DJPackage.MODIFIES_CLASS__CLASS:
        setClass((org.xtext.example.dJ.Class)null);
        return;
      case DJPackage.MODIFIES_CLASS__EXTENDS:
        setExtends((org.xtext.example.dJ.Class)null);
        return;
      case DJPackage.MODIFIES_CLASS__FIELD:
        setField((Fieldm)null);
        return;
      case DJPackage.MODIFIES_CLASS__CONSTRUCTOR:
        setConstructor((Constructor)null);
        return;
      case DJPackage.MODIFIES_CLASS__METHOD:
        setMethod((Methodm)null);
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
      case DJPackage.MODIFIES_CLASS__CLASS:
        return class_ != null;
      case DJPackage.MODIFIES_CLASS__EXTENDS:
        return extends_ != null;
      case DJPackage.MODIFIES_CLASS__FIELD:
        return field != null;
      case DJPackage.MODIFIES_CLASS__CONSTRUCTOR:
        return constructor != null;
      case DJPackage.MODIFIES_CLASS__METHOD:
        return method != null;
    }
    return super.eIsSet(featureID);
  }

} //ModifiesClassImpl
