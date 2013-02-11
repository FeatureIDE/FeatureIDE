package org.xtext.example.util;

import org.eclipse.emf.ecore.EObject;
import org.xtext.example.dJ.Class;
import org.xtext.example.dJ.*;
import org.xtext.example.dJ.util.DJSwitch;

public class ContainingModuleFinded extends DJSwitch<Module>
{
	  public Module lookup(ModifiesClass c)
	  {
	    EObject current = c;
	    EObject owner = null;
	    while (owner == null) {
	      current = current.eContainer();
	      owner = (EObject)doSwitch(current);
		    if (current.eContainer() == null) return null;
	    }

	    return (Module)owner;
	  }
	  public Module lookup(MethodBody c)
	  {
	    EObject current = c;
	    EObject owner = null;
	    while (owner == null) {
	      current = current.eContainer();
	      owner = (EObject)doSwitch(current);
		    if (current.eContainer() == null) return null;
	    }

	    return (Module)owner;
	  }
  public Module lookup(Class c) {
	  	if (c == null) return null;
	    EObject current = c;
	    EObject owner = null;
	    //FIX ME XTEXT
	    while (owner == null) {
	      current = current.eContainer();
	      if(current == null) return null; //NEW
	      owner = (EObject)doSwitch(current);
		  //if (current.eContainer() == null) return null;
	    }

	    return (Module)owner;
	  }
  public Module lookup(Parameter c) {
	    EObject current = c;
	    EObject owner = null;
	    //FIX ME XTEXT
	    while (owner == null) {
	      current = current.eContainer();
	      if(current == null) return null; //NEW
	      owner = (EObject)doSwitch(current);
		  //if (current.eContainer() == null) return null;
	    }

	    return (Module)owner;
	  }
  public Module lookup(AddsClass c) {
    EObject current = c;
    EObject owner = null;
    //FIX ME XTEXT
    while (owner == null) {
      current = current.eContainer();
      if(current == null) return null; //NEW
      owner = (EObject)doSwitch(current);
	  //if (current.eContainer() == null) return null;
    }

    return (Module)owner;
  }
  public Module lookup(RemoveClass c) {
    EObject current = c;
    EObject owner = null;
    //FIX ME XTEXT
    while (owner == null) {
      current = current.eContainer();
      if(current == null) return null; //NEW
      owner = (EObject)doSwitch(current);
	  //if (current.eContainer() == null) return null;
    }

    return (Module)owner;
  }
  public Module lookup(Classm c) {
    EObject current = c;
    EObject owner = null;
    //FIX ME XTEXT
    while (owner == null) {
      current = current.eContainer();
      if(current == null) return null; //NEW
      owner = (EObject)doSwitch(current);
	  //if (current.eContainer() == null) return null;
    }

    return (Module)owner;
  }

  public Module caseModule(Module module) {
    return module;
  }
}