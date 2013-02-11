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

import org.xtext.example.dJ.Cast;
import org.xtext.example.dJ.DJPackage;
import org.xtext.example.dJ.Intero;
import org.xtext.example.dJ.New;
import org.xtext.example.dJ.Nullo;
import org.xtext.example.dJ.Original;
import org.xtext.example.dJ.Stringa;
import org.xtext.example.dJ.TerminalExpression;
import org.xtext.example.dJ.This;
import org.xtext.example.dJ.Variable;

/**
 * <!-- begin-user-doc -->
 * An implementation of the model object '<em><b>Terminal Expression</b></em>'.
 * <!-- end-user-doc -->
 * <p>
 * The following features are implemented:
 * <ul>
 *   <li>{@link org.xtext.example.dJ.impl.TerminalExpressionImpl#getThis <em>This</em>}</li>
 *   <li>{@link org.xtext.example.dJ.impl.TerminalExpressionImpl#getVariable <em>Variable</em>}</li>
 *   <li>{@link org.xtext.example.dJ.impl.TerminalExpressionImpl#getNew <em>New</em>}</li>
 *   <li>{@link org.xtext.example.dJ.impl.TerminalExpressionImpl#getCast <em>Cast</em>}</li>
 *   <li>{@link org.xtext.example.dJ.impl.TerminalExpressionImpl#getOriginal <em>Original</em>}</li>
 *   <li>{@link org.xtext.example.dJ.impl.TerminalExpressionImpl#getInt <em>Int</em>}</li>
 *   <li>{@link org.xtext.example.dJ.impl.TerminalExpressionImpl#getString <em>String</em>}</li>
 *   <li>{@link org.xtext.example.dJ.impl.TerminalExpressionImpl#getNull <em>Null</em>}</li>
 * </ul>
 * </p>
 *
 * @generated
 */
public class TerminalExpressionImpl extends MinimalEObjectImpl.Container implements TerminalExpression
{
  /**
   * The cached value of the '{@link #getThis() <em>This</em>}' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see #getThis()
   * @generated
   * @ordered
   */
  protected This this_;

  /**
   * The cached value of the '{@link #getVariable() <em>Variable</em>}' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see #getVariable()
   * @generated
   * @ordered
   */
  protected Variable variable;

  /**
   * The cached value of the '{@link #getNew() <em>New</em>}' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see #getNew()
   * @generated
   * @ordered
   */
  protected New new_;

  /**
   * The cached value of the '{@link #getCast() <em>Cast</em>}' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see #getCast()
   * @generated
   * @ordered
   */
  protected Cast cast;

  /**
   * The cached value of the '{@link #getOriginal() <em>Original</em>}' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see #getOriginal()
   * @generated
   * @ordered
   */
  protected Original original;

  /**
   * The cached value of the '{@link #getInt() <em>Int</em>}' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see #getInt()
   * @generated
   * @ordered
   */
  protected Intero int_;

  /**
   * The cached value of the '{@link #getString() <em>String</em>}' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see #getString()
   * @generated
   * @ordered
   */
  protected Stringa string;

  /**
   * The cached value of the '{@link #getNull() <em>Null</em>}' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see #getNull()
   * @generated
   * @ordered
   */
  protected Nullo null_;

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  protected TerminalExpressionImpl()
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
    return DJPackage.Literals.TERMINAL_EXPRESSION;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public This getThis()
  {
    return this_;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public NotificationChain basicSetThis(This newThis, NotificationChain msgs)
  {
    This oldThis = this_;
    this_ = newThis;
    if (eNotificationRequired())
    {
      ENotificationImpl notification = new ENotificationImpl(this, Notification.SET, DJPackage.TERMINAL_EXPRESSION__THIS, oldThis, newThis);
      if (msgs == null) msgs = notification; else msgs.add(notification);
    }
    return msgs;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public void setThis(This newThis)
  {
    if (newThis != this_)
    {
      NotificationChain msgs = null;
      if (this_ != null)
        msgs = ((InternalEObject)this_).eInverseRemove(this, EOPPOSITE_FEATURE_BASE - DJPackage.TERMINAL_EXPRESSION__THIS, null, msgs);
      if (newThis != null)
        msgs = ((InternalEObject)newThis).eInverseAdd(this, EOPPOSITE_FEATURE_BASE - DJPackage.TERMINAL_EXPRESSION__THIS, null, msgs);
      msgs = basicSetThis(newThis, msgs);
      if (msgs != null) msgs.dispatch();
    }
    else if (eNotificationRequired())
      eNotify(new ENotificationImpl(this, Notification.SET, DJPackage.TERMINAL_EXPRESSION__THIS, newThis, newThis));
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public Variable getVariable()
  {
    return variable;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public NotificationChain basicSetVariable(Variable newVariable, NotificationChain msgs)
  {
    Variable oldVariable = variable;
    variable = newVariable;
    if (eNotificationRequired())
    {
      ENotificationImpl notification = new ENotificationImpl(this, Notification.SET, DJPackage.TERMINAL_EXPRESSION__VARIABLE, oldVariable, newVariable);
      if (msgs == null) msgs = notification; else msgs.add(notification);
    }
    return msgs;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public void setVariable(Variable newVariable)
  {
    if (newVariable != variable)
    {
      NotificationChain msgs = null;
      if (variable != null)
        msgs = ((InternalEObject)variable).eInverseRemove(this, EOPPOSITE_FEATURE_BASE - DJPackage.TERMINAL_EXPRESSION__VARIABLE, null, msgs);
      if (newVariable != null)
        msgs = ((InternalEObject)newVariable).eInverseAdd(this, EOPPOSITE_FEATURE_BASE - DJPackage.TERMINAL_EXPRESSION__VARIABLE, null, msgs);
      msgs = basicSetVariable(newVariable, msgs);
      if (msgs != null) msgs.dispatch();
    }
    else if (eNotificationRequired())
      eNotify(new ENotificationImpl(this, Notification.SET, DJPackage.TERMINAL_EXPRESSION__VARIABLE, newVariable, newVariable));
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public New getNew()
  {
    return new_;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public NotificationChain basicSetNew(New newNew, NotificationChain msgs)
  {
    New oldNew = new_;
    new_ = newNew;
    if (eNotificationRequired())
    {
      ENotificationImpl notification = new ENotificationImpl(this, Notification.SET, DJPackage.TERMINAL_EXPRESSION__NEW, oldNew, newNew);
      if (msgs == null) msgs = notification; else msgs.add(notification);
    }
    return msgs;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public void setNew(New newNew)
  {
    if (newNew != new_)
    {
      NotificationChain msgs = null;
      if (new_ != null)
        msgs = ((InternalEObject)new_).eInverseRemove(this, EOPPOSITE_FEATURE_BASE - DJPackage.TERMINAL_EXPRESSION__NEW, null, msgs);
      if (newNew != null)
        msgs = ((InternalEObject)newNew).eInverseAdd(this, EOPPOSITE_FEATURE_BASE - DJPackage.TERMINAL_EXPRESSION__NEW, null, msgs);
      msgs = basicSetNew(newNew, msgs);
      if (msgs != null) msgs.dispatch();
    }
    else if (eNotificationRequired())
      eNotify(new ENotificationImpl(this, Notification.SET, DJPackage.TERMINAL_EXPRESSION__NEW, newNew, newNew));
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public Cast getCast()
  {
    return cast;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public NotificationChain basicSetCast(Cast newCast, NotificationChain msgs)
  {
    Cast oldCast = cast;
    cast = newCast;
    if (eNotificationRequired())
    {
      ENotificationImpl notification = new ENotificationImpl(this, Notification.SET, DJPackage.TERMINAL_EXPRESSION__CAST, oldCast, newCast);
      if (msgs == null) msgs = notification; else msgs.add(notification);
    }
    return msgs;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public void setCast(Cast newCast)
  {
    if (newCast != cast)
    {
      NotificationChain msgs = null;
      if (cast != null)
        msgs = ((InternalEObject)cast).eInverseRemove(this, EOPPOSITE_FEATURE_BASE - DJPackage.TERMINAL_EXPRESSION__CAST, null, msgs);
      if (newCast != null)
        msgs = ((InternalEObject)newCast).eInverseAdd(this, EOPPOSITE_FEATURE_BASE - DJPackage.TERMINAL_EXPRESSION__CAST, null, msgs);
      msgs = basicSetCast(newCast, msgs);
      if (msgs != null) msgs.dispatch();
    }
    else if (eNotificationRequired())
      eNotify(new ENotificationImpl(this, Notification.SET, DJPackage.TERMINAL_EXPRESSION__CAST, newCast, newCast));
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public Original getOriginal()
  {
    return original;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public NotificationChain basicSetOriginal(Original newOriginal, NotificationChain msgs)
  {
    Original oldOriginal = original;
    original = newOriginal;
    if (eNotificationRequired())
    {
      ENotificationImpl notification = new ENotificationImpl(this, Notification.SET, DJPackage.TERMINAL_EXPRESSION__ORIGINAL, oldOriginal, newOriginal);
      if (msgs == null) msgs = notification; else msgs.add(notification);
    }
    return msgs;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public void setOriginal(Original newOriginal)
  {
    if (newOriginal != original)
    {
      NotificationChain msgs = null;
      if (original != null)
        msgs = ((InternalEObject)original).eInverseRemove(this, EOPPOSITE_FEATURE_BASE - DJPackage.TERMINAL_EXPRESSION__ORIGINAL, null, msgs);
      if (newOriginal != null)
        msgs = ((InternalEObject)newOriginal).eInverseAdd(this, EOPPOSITE_FEATURE_BASE - DJPackage.TERMINAL_EXPRESSION__ORIGINAL, null, msgs);
      msgs = basicSetOriginal(newOriginal, msgs);
      if (msgs != null) msgs.dispatch();
    }
    else if (eNotificationRequired())
      eNotify(new ENotificationImpl(this, Notification.SET, DJPackage.TERMINAL_EXPRESSION__ORIGINAL, newOriginal, newOriginal));
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public Intero getInt()
  {
    return int_;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public NotificationChain basicSetInt(Intero newInt, NotificationChain msgs)
  {
    Intero oldInt = int_;
    int_ = newInt;
    if (eNotificationRequired())
    {
      ENotificationImpl notification = new ENotificationImpl(this, Notification.SET, DJPackage.TERMINAL_EXPRESSION__INT, oldInt, newInt);
      if (msgs == null) msgs = notification; else msgs.add(notification);
    }
    return msgs;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public void setInt(Intero newInt)
  {
    if (newInt != int_)
    {
      NotificationChain msgs = null;
      if (int_ != null)
        msgs = ((InternalEObject)int_).eInverseRemove(this, EOPPOSITE_FEATURE_BASE - DJPackage.TERMINAL_EXPRESSION__INT, null, msgs);
      if (newInt != null)
        msgs = ((InternalEObject)newInt).eInverseAdd(this, EOPPOSITE_FEATURE_BASE - DJPackage.TERMINAL_EXPRESSION__INT, null, msgs);
      msgs = basicSetInt(newInt, msgs);
      if (msgs != null) msgs.dispatch();
    }
    else if (eNotificationRequired())
      eNotify(new ENotificationImpl(this, Notification.SET, DJPackage.TERMINAL_EXPRESSION__INT, newInt, newInt));
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public Stringa getString()
  {
    return string;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public NotificationChain basicSetString(Stringa newString, NotificationChain msgs)
  {
    Stringa oldString = string;
    string = newString;
    if (eNotificationRequired())
    {
      ENotificationImpl notification = new ENotificationImpl(this, Notification.SET, DJPackage.TERMINAL_EXPRESSION__STRING, oldString, newString);
      if (msgs == null) msgs = notification; else msgs.add(notification);
    }
    return msgs;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public void setString(Stringa newString)
  {
    if (newString != string)
    {
      NotificationChain msgs = null;
      if (string != null)
        msgs = ((InternalEObject)string).eInverseRemove(this, EOPPOSITE_FEATURE_BASE - DJPackage.TERMINAL_EXPRESSION__STRING, null, msgs);
      if (newString != null)
        msgs = ((InternalEObject)newString).eInverseAdd(this, EOPPOSITE_FEATURE_BASE - DJPackage.TERMINAL_EXPRESSION__STRING, null, msgs);
      msgs = basicSetString(newString, msgs);
      if (msgs != null) msgs.dispatch();
    }
    else if (eNotificationRequired())
      eNotify(new ENotificationImpl(this, Notification.SET, DJPackage.TERMINAL_EXPRESSION__STRING, newString, newString));
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public Nullo getNull()
  {
    return null_;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public NotificationChain basicSetNull(Nullo newNull, NotificationChain msgs)
  {
    Nullo oldNull = null_;
    null_ = newNull;
    if (eNotificationRequired())
    {
      ENotificationImpl notification = new ENotificationImpl(this, Notification.SET, DJPackage.TERMINAL_EXPRESSION__NULL, oldNull, newNull);
      if (msgs == null) msgs = notification; else msgs.add(notification);
    }
    return msgs;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public void setNull(Nullo newNull)
  {
    if (newNull != null_)
    {
      NotificationChain msgs = null;
      if (null_ != null)
        msgs = ((InternalEObject)null_).eInverseRemove(this, EOPPOSITE_FEATURE_BASE - DJPackage.TERMINAL_EXPRESSION__NULL, null, msgs);
      if (newNull != null)
        msgs = ((InternalEObject)newNull).eInverseAdd(this, EOPPOSITE_FEATURE_BASE - DJPackage.TERMINAL_EXPRESSION__NULL, null, msgs);
      msgs = basicSetNull(newNull, msgs);
      if (msgs != null) msgs.dispatch();
    }
    else if (eNotificationRequired())
      eNotify(new ENotificationImpl(this, Notification.SET, DJPackage.TERMINAL_EXPRESSION__NULL, newNull, newNull));
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
      case DJPackage.TERMINAL_EXPRESSION__THIS:
        return basicSetThis(null, msgs);
      case DJPackage.TERMINAL_EXPRESSION__VARIABLE:
        return basicSetVariable(null, msgs);
      case DJPackage.TERMINAL_EXPRESSION__NEW:
        return basicSetNew(null, msgs);
      case DJPackage.TERMINAL_EXPRESSION__CAST:
        return basicSetCast(null, msgs);
      case DJPackage.TERMINAL_EXPRESSION__ORIGINAL:
        return basicSetOriginal(null, msgs);
      case DJPackage.TERMINAL_EXPRESSION__INT:
        return basicSetInt(null, msgs);
      case DJPackage.TERMINAL_EXPRESSION__STRING:
        return basicSetString(null, msgs);
      case DJPackage.TERMINAL_EXPRESSION__NULL:
        return basicSetNull(null, msgs);
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
      case DJPackage.TERMINAL_EXPRESSION__THIS:
        return getThis();
      case DJPackage.TERMINAL_EXPRESSION__VARIABLE:
        return getVariable();
      case DJPackage.TERMINAL_EXPRESSION__NEW:
        return getNew();
      case DJPackage.TERMINAL_EXPRESSION__CAST:
        return getCast();
      case DJPackage.TERMINAL_EXPRESSION__ORIGINAL:
        return getOriginal();
      case DJPackage.TERMINAL_EXPRESSION__INT:
        return getInt();
      case DJPackage.TERMINAL_EXPRESSION__STRING:
        return getString();
      case DJPackage.TERMINAL_EXPRESSION__NULL:
        return getNull();
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
      case DJPackage.TERMINAL_EXPRESSION__THIS:
        setThis((This)newValue);
        return;
      case DJPackage.TERMINAL_EXPRESSION__VARIABLE:
        setVariable((Variable)newValue);
        return;
      case DJPackage.TERMINAL_EXPRESSION__NEW:
        setNew((New)newValue);
        return;
      case DJPackage.TERMINAL_EXPRESSION__CAST:
        setCast((Cast)newValue);
        return;
      case DJPackage.TERMINAL_EXPRESSION__ORIGINAL:
        setOriginal((Original)newValue);
        return;
      case DJPackage.TERMINAL_EXPRESSION__INT:
        setInt((Intero)newValue);
        return;
      case DJPackage.TERMINAL_EXPRESSION__STRING:
        setString((Stringa)newValue);
        return;
      case DJPackage.TERMINAL_EXPRESSION__NULL:
        setNull((Nullo)newValue);
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
      case DJPackage.TERMINAL_EXPRESSION__THIS:
        setThis((This)null);
        return;
      case DJPackage.TERMINAL_EXPRESSION__VARIABLE:
        setVariable((Variable)null);
        return;
      case DJPackage.TERMINAL_EXPRESSION__NEW:
        setNew((New)null);
        return;
      case DJPackage.TERMINAL_EXPRESSION__CAST:
        setCast((Cast)null);
        return;
      case DJPackage.TERMINAL_EXPRESSION__ORIGINAL:
        setOriginal((Original)null);
        return;
      case DJPackage.TERMINAL_EXPRESSION__INT:
        setInt((Intero)null);
        return;
      case DJPackage.TERMINAL_EXPRESSION__STRING:
        setString((Stringa)null);
        return;
      case DJPackage.TERMINAL_EXPRESSION__NULL:
        setNull((Nullo)null);
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
      case DJPackage.TERMINAL_EXPRESSION__THIS:
        return this_ != null;
      case DJPackage.TERMINAL_EXPRESSION__VARIABLE:
        return variable != null;
      case DJPackage.TERMINAL_EXPRESSION__NEW:
        return new_ != null;
      case DJPackage.TERMINAL_EXPRESSION__CAST:
        return cast != null;
      case DJPackage.TERMINAL_EXPRESSION__ORIGINAL:
        return original != null;
      case DJPackage.TERMINAL_EXPRESSION__INT:
        return int_ != null;
      case DJPackage.TERMINAL_EXPRESSION__STRING:
        return string != null;
      case DJPackage.TERMINAL_EXPRESSION__NULL:
        return null_ != null;
    }
    return super.eIsSet(featureID);
  }

} //TerminalExpressionImpl
