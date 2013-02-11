package org.xtext.example.util;

import org.eclipse.emf.ecore.EObject;
import org.xtext.example.dJ.*;
import org.xtext.example.dJ.util.DJSwitch;

public class ContainingModifiesMethodFinded extends DJSwitch<ModifiesMethod>
{
  private boolean end = false;

  public ModifiesMethod lookup(Original e) { EObject current = e;
    EObject owner = null;
    while ((owner == null) && (!end)) {
      current = current.eContainer();
      owner = (EObject)doSwitch(current);
    }
    return (ModifiesMethod)owner; }
  
  public ModifiesMethod lookup(Argument e) { 
	  EObject current = e;
	  EObject owner = null;
	  while ((owner == null) && (!this.end)) {
	    current = current.eContainer();
	    owner = (EObject)doSwitch(current);
	    if (current.eContainer() == null) return null;
	  }
	  return (ModifiesMethod)owner;
  }
  public ModifiesMethod lookup(MethodRef e) { 
	  EObject current = e;
	  EObject owner = null;
	  while ((owner == null) && (!this.end)) {
	    current = current.eContainer();
	    owner = (EObject)doSwitch(current);
	    if (current.eContainer() == null) return null;
	  }
	  return (ModifiesMethod)owner;
  }
	  
  public ModifiesMethod caseModifiesMethod(ModifiesMethod mMethod)
  {
    return mMethod;
  }
  public ModifiesMethod caseModule(Module module) {
	  this.end = true;
	  return null;
  }
}