package org.xtext.example.util;

import org.eclipse.emf.ecore.EObject;
import org.xtext.example.dJ.*;
import org.xtext.example.dJ.util.DJSwitch;

public class ContainingExpressionFinded extends DJSwitch<Expression>
{
  public Expression lookup(FieldAccess e)
  {
    EObject current = e;
    EObject owner = null;
    while (owner == null) {
      current = current.eContainer();
      owner = (EObject)doSwitch(current);
      if (current.eContainer() == null) return null;
    }

    return (Expression)owner;
  }
  public Expression lookup(MethodCall e) {
    EObject current = e;
    EObject owner = null;
    while (owner == null) {
      current = current.eContainer();
      owner = (EObject)doSwitch(current);
      if (current.eContainer() == null) return null;
    }

    return (Expression)owner;
  }

  public Expression caseExpression(Expression e) {
    return e;
  }
}