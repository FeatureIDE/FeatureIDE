/**
 * <copyright>
 * </copyright>
 *
 */
package org.deltaj.deltaj.impl;

import java.util.Collection;

import org.deltaj.deltaj.DeltajPackage;
import org.deltaj.deltaj.LocalVariableDeclaration;
import org.deltaj.deltaj.Statement;
import org.deltaj.deltaj.StatementBlock;

import org.eclipse.emf.common.notify.NotificationChain;

import org.eclipse.emf.common.util.EList;

import org.eclipse.emf.ecore.EClass;
import org.eclipse.emf.ecore.InternalEObject;

import org.eclipse.emf.ecore.impl.MinimalEObjectImpl;

import org.eclipse.emf.ecore.util.EObjectContainmentEList;
import org.eclipse.emf.ecore.util.InternalEList;

/**
 * <!-- begin-user-doc -->
 * An implementation of the model object '<em><b>Statement Block</b></em>'.
 * <!-- end-user-doc -->
 * <p>
 * The following features are implemented:
 * <ul>
 *   <li>{@link org.deltaj.deltaj.impl.StatementBlockImpl#getLocalvariables <em>Localvariables</em>}</li>
 *   <li>{@link org.deltaj.deltaj.impl.StatementBlockImpl#getStatements <em>Statements</em>}</li>
 * </ul>
 * </p>
 *
 * @generated
 */
public class StatementBlockImpl extends MinimalEObjectImpl.Container implements StatementBlock
{
  /**
   * The cached value of the '{@link #getLocalvariables() <em>Localvariables</em>}' containment reference list.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see #getLocalvariables()
   * @generated
   * @ordered
   */
  protected EList<LocalVariableDeclaration> localvariables;

  /**
   * The cached value of the '{@link #getStatements() <em>Statements</em>}' containment reference list.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @see #getStatements()
   * @generated
   * @ordered
   */
  protected EList<Statement> statements;

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  protected StatementBlockImpl()
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
    return DeltajPackage.Literals.STATEMENT_BLOCK;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public EList<LocalVariableDeclaration> getLocalvariables()
  {
    if (localvariables == null)
    {
      localvariables = new EObjectContainmentEList<LocalVariableDeclaration>(LocalVariableDeclaration.class, this, DeltajPackage.STATEMENT_BLOCK__LOCALVARIABLES);
    }
    return localvariables;
  }

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  public EList<Statement> getStatements()
  {
    if (statements == null)
    {
      statements = new EObjectContainmentEList<Statement>(Statement.class, this, DeltajPackage.STATEMENT_BLOCK__STATEMENTS);
    }
    return statements;
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
      case DeltajPackage.STATEMENT_BLOCK__LOCALVARIABLES:
        return ((InternalEList<?>)getLocalvariables()).basicRemove(otherEnd, msgs);
      case DeltajPackage.STATEMENT_BLOCK__STATEMENTS:
        return ((InternalEList<?>)getStatements()).basicRemove(otherEnd, msgs);
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
      case DeltajPackage.STATEMENT_BLOCK__LOCALVARIABLES:
        return getLocalvariables();
      case DeltajPackage.STATEMENT_BLOCK__STATEMENTS:
        return getStatements();
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
      case DeltajPackage.STATEMENT_BLOCK__LOCALVARIABLES:
        getLocalvariables().clear();
        getLocalvariables().addAll((Collection<? extends LocalVariableDeclaration>)newValue);
        return;
      case DeltajPackage.STATEMENT_BLOCK__STATEMENTS:
        getStatements().clear();
        getStatements().addAll((Collection<? extends Statement>)newValue);
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
      case DeltajPackage.STATEMENT_BLOCK__LOCALVARIABLES:
        getLocalvariables().clear();
        return;
      case DeltajPackage.STATEMENT_BLOCK__STATEMENTS:
        getStatements().clear();
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
      case DeltajPackage.STATEMENT_BLOCK__LOCALVARIABLES:
        return localvariables != null && !localvariables.isEmpty();
      case DeltajPackage.STATEMENT_BLOCK__STATEMENTS:
        return statements != null && !statements.isEmpty();
    }
    return super.eIsSet(featureID);
  }

} //StatementBlockImpl
