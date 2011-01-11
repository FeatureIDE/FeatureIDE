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
import org.xtext.example.dJ.Expression;
import org.xtext.example.dJ.InsertJava;
import org.xtext.example.dJ.MethodBody;

/**
 * <!-- begin-user-doc -->
 * An implementation of the model object '<em><b>Method Body</b></em>'.
 * <!-- end-user-doc -->
 * <p>
 * The following features are implemented:
 * <ul>
 *   <li>{@link org.xtext.example.dJ.impl.MethodBodyImpl#getInsertJava <em>Insert Java</em>}</li>
 *   <li>{@link org.xtext.example.dJ.impl.MethodBodyImpl#getExpressions <em>Expressions</em>}</li>
 *   <li>{@link org.xtext.example.dJ.impl.MethodBodyImpl#getReturn <em>Return</em>}</li>
 *   <li>{@link org.xtext.example.dJ.impl.MethodBodyImpl#getExpressionReturn <em>Expression Return</em>}</li>
 * </ul>
 * </p>
 *
 * @generated
 */
public class MethodBodyImpl extends MinimalEObjectImpl.Container implements MethodBody
{
  /**
   * The cached value of the '{@link #getInsertJava() <em>Insert Java</em>}' containment reference list.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see #getInsertJava()
   * @generated
   * @ordered
   */
  protected EList<InsertJava> insertJava;

  /**
   * The cached value of the '{@link #getExpressions() <em>Expressions</em>}' containment reference list.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see #getExpressions()
   * @generated
   * @ordered
   */
  protected EList<Expression> expressions;

  /**
   * The default value of the '{@link #getReturn() <em>Return</em>}' attribute.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see #getReturn()
   * @generated
   * @ordered
   */
  protected static final String RETURN_EDEFAULT = null;

  /**
   * The cached value of the '{@link #getReturn() <em>Return</em>}' attribute.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see #getReturn()
   * @generated
   * @ordered
   */
  protected String return_ = RETURN_EDEFAULT;

  /**
   * The cached value of the '{@link #getExpressionReturn() <em>Expression Return</em>}' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see #getExpressionReturn()
   * @generated
   * @ordered
   */
  protected Expression expressionReturn;

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  protected MethodBodyImpl()
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
    return DJPackage.Literals.METHOD_BODY;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public EList<InsertJava> getInsertJava()
  {
    if (insertJava == null)
    {
      insertJava = new EObjectContainmentEList<InsertJava>(InsertJava.class, this, DJPackage.METHOD_BODY__INSERT_JAVA);
    }
    return insertJava;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public EList<Expression> getExpressions()
  {
    if (expressions == null)
    {
      expressions = new EObjectContainmentEList<Expression>(Expression.class, this, DJPackage.METHOD_BODY__EXPRESSIONS);
    }
    return expressions;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public String getReturn()
  {
    return return_;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public void setReturn(String newReturn)
  {
    String oldReturn = return_;
    return_ = newReturn;
    if (eNotificationRequired())
      eNotify(new ENotificationImpl(this, Notification.SET, DJPackage.METHOD_BODY__RETURN, oldReturn, return_));
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public Expression getExpressionReturn()
  {
    return expressionReturn;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public NotificationChain basicSetExpressionReturn(Expression newExpressionReturn, NotificationChain msgs)
  {
    Expression oldExpressionReturn = expressionReturn;
    expressionReturn = newExpressionReturn;
    if (eNotificationRequired())
    {
      ENotificationImpl notification = new ENotificationImpl(this, Notification.SET, DJPackage.METHOD_BODY__EXPRESSION_RETURN, oldExpressionReturn, newExpressionReturn);
      if (msgs == null) msgs = notification; else msgs.add(notification);
    }
    return msgs;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public void setExpressionReturn(Expression newExpressionReturn)
  {
    if (newExpressionReturn != expressionReturn)
    {
      NotificationChain msgs = null;
      if (expressionReturn != null)
        msgs = ((InternalEObject)expressionReturn).eInverseRemove(this, EOPPOSITE_FEATURE_BASE - DJPackage.METHOD_BODY__EXPRESSION_RETURN, null, msgs);
      if (newExpressionReturn != null)
        msgs = ((InternalEObject)newExpressionReturn).eInverseAdd(this, EOPPOSITE_FEATURE_BASE - DJPackage.METHOD_BODY__EXPRESSION_RETURN, null, msgs);
      msgs = basicSetExpressionReturn(newExpressionReturn, msgs);
      if (msgs != null) msgs.dispatch();
    }
    else if (eNotificationRequired())
      eNotify(new ENotificationImpl(this, Notification.SET, DJPackage.METHOD_BODY__EXPRESSION_RETURN, newExpressionReturn, newExpressionReturn));
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
      case DJPackage.METHOD_BODY__INSERT_JAVA:
        return ((InternalEList<?>)getInsertJava()).basicRemove(otherEnd, msgs);
      case DJPackage.METHOD_BODY__EXPRESSIONS:
        return ((InternalEList<?>)getExpressions()).basicRemove(otherEnd, msgs);
      case DJPackage.METHOD_BODY__EXPRESSION_RETURN:
        return basicSetExpressionReturn(null, msgs);
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
      case DJPackage.METHOD_BODY__INSERT_JAVA:
        return getInsertJava();
      case DJPackage.METHOD_BODY__EXPRESSIONS:
        return getExpressions();
      case DJPackage.METHOD_BODY__RETURN:
        return getReturn();
      case DJPackage.METHOD_BODY__EXPRESSION_RETURN:
        return getExpressionReturn();
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
      case DJPackage.METHOD_BODY__INSERT_JAVA:
        getInsertJava().clear();
        getInsertJava().addAll((Collection<? extends InsertJava>)newValue);
        return;
      case DJPackage.METHOD_BODY__EXPRESSIONS:
        getExpressions().clear();
        getExpressions().addAll((Collection<? extends Expression>)newValue);
        return;
      case DJPackage.METHOD_BODY__RETURN:
        setReturn((String)newValue);
        return;
      case DJPackage.METHOD_BODY__EXPRESSION_RETURN:
        setExpressionReturn((Expression)newValue);
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
      case DJPackage.METHOD_BODY__INSERT_JAVA:
        getInsertJava().clear();
        return;
      case DJPackage.METHOD_BODY__EXPRESSIONS:
        getExpressions().clear();
        return;
      case DJPackage.METHOD_BODY__RETURN:
        setReturn(RETURN_EDEFAULT);
        return;
      case DJPackage.METHOD_BODY__EXPRESSION_RETURN:
        setExpressionReturn((Expression)null);
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
      case DJPackage.METHOD_BODY__INSERT_JAVA:
        return insertJava != null && !insertJava.isEmpty();
      case DJPackage.METHOD_BODY__EXPRESSIONS:
        return expressions != null && !expressions.isEmpty();
      case DJPackage.METHOD_BODY__RETURN:
        return RETURN_EDEFAULT == null ? return_ != null : !RETURN_EDEFAULT.equals(return_);
      case DJPackage.METHOD_BODY__EXPRESSION_RETURN:
        return expressionReturn != null;
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
    result.append(" (return: ");
    result.append(return_);
    result.append(')');
    return result.toString();
  }

} //MethodBodyImpl
