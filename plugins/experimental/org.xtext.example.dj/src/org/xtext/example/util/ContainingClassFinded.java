package org.xtext.example.util;

import org.eclipse.emf.ecore.EObject;
import org.xtext.example.dJ.Class;
import org.xtext.example.dJ.*;
import org.xtext.example.dJ.util.DJSwitch;

public class ContainingClassFinded extends DJSwitch<Class>
{
  public Class lookup(Constructor e)
  {
    EObject current = e;
    EObject owner = null;
    while (owner == null) {
      current = current.eContainer();
      owner = (EObject)doSwitch(current);
      if (current.eContainer() == null) return null;
    }
    return (Class)owner;
  }
  public Class lookup(FieldRef e) {
    EObject current = e;
    EObject owner = null;
    while ((owner == null) && (current.eContainer() != null)) {
      current = current.eContainer();
      owner = (EObject)doSwitch(current);
      if (current.eContainer() == null) return null;
    }
    return (Class)owner;
  }
  public Class lookup(MethodRef e) {
    EObject current = e;
    EObject owner = null;
    while ((owner == null) && (current.eContainer() != null)) {
      current = current.eContainer();
      owner = (EObject)doSwitch(current);
      if (current.eContainer() == null) return null;
    }
    return (Class)owner;
  }
  public Class lookup(TerminalExpression e) {
    EObject current = e;
    EObject owner = null;
    while (owner == null) {
      current = current.eContainer();
      owner = (EObject)doSwitch(current);
      if (current.eContainer() == null) return null;
    }
    return (Class)owner;
  }

  public Class caseClass(Class c) {
    return c;
  }
}