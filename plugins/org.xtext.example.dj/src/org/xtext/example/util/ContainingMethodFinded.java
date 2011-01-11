package org.xtext.example.util;

import org.eclipse.emf.ecore.EObject;
import org.xtext.example.dJ.*;
import org.xtext.example.dJ.util.DJSwitch;


public class ContainingMethodFinded extends DJSwitch<Method>
{
  private boolean end = false;

  public Method lookup(Original e) { EObject current = e;
    EObject owner = null;
    while ((owner == null) && (!this.end)) {
      current = current.eContainer();
      owner = (EObject)doSwitch(current);
    }

    return (Method)owner; 
  }

  public Method lookup(Argument e) { 
	  EObject current = e;
	  EObject owner = null;
	  while ((owner == null) && (!this.end)) {
	    current = current.eContainer();
	    owner = (EObject)doSwitch(current);
	    if (current.eContainer() == null) return null;
	  }

	  return (Method)owner; 
	  }
  public Method lookup(MethodRef e) { 
	  EObject current = e;
	  EObject owner = null;
	  while ((owner == null) && (!this.end)) {
	    current = current.eContainer();
	    owner = (EObject)doSwitch(current);
	    if (current.eContainer() == null) return null;
	  }

	  return (Method)owner; 
  }
  
  public Method caseMethod(Method mMethod)
  {
    return mMethod;
  }
  public Method caseModule(Module module) {
    this.end = true;
    return null;
  }
}