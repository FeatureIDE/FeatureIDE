package org.xtext.example.util;

import org.eclipse.emf.ecore.EObject;
import org.xtext.example.dJ.Class;
import org.xtext.example.dJ.*;
import org.xtext.example.dJ.util.DJSwitch;

public class ContainingClassmFinded extends DJSwitch<Classm>
{
  public Classm lookup(Class c)
  {
    EObject current = c;
    EObject owner = null;
    while (owner == null) {
      current = current.eContainer();
      owner = (EObject)doSwitch(current);
      if (current.eContainer() == null) return null;
    }

    return (Classm)owner;
  }

  public Classm lookup(Constructor e) {
    EObject current = e;
    EObject owner = null;
    while (owner == null) {
      current = current.eContainer();
      owner = (EObject)doSwitch(current);
      if (current.eContainer() == null) return null;
    }

    return (Classm)owner;
  }
  public Classm lookup(FieldRef e) {
    EObject current = e;
    EObject owner = null;
    while (owner == null) {
      current = current.eContainer();
      owner = (EObject)doSwitch(current);
      if (current.eContainer() == null) return null;
    }

    return (Classm)owner;
  }
  public Classm lookup(MethodRef e) {
    EObject current = e;
    EObject owner = null;
    while (owner == null) {
      current = current.eContainer();
      owner = (EObject)doSwitch(current);
      if (current.eContainer() == null) return null;
    }

    return (Classm)owner;
  }
  @SuppressWarnings("unused")
public Classm lookup(TerminalExpression e) {
	EObject current = e;
    EObject owner = null;
    int a = 0;
    while (owner == null) {
      current = current.eContainer();
      owner = (EObject)doSwitch(current);
      if (current.eContainer() == null) return null;
    }

    return (Classm)owner;
  }

  public Classm caseClassm(Classm classm) {
    return classm;
  }
}