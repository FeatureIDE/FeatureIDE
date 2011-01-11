package org.xtext.example.util;

import org.eclipse.emf.ecore.EObject;
import org.xtext.example.dJ.Argument;
import org.xtext.example.dJ.Class;
import org.xtext.example.dJ.Constructor;
import org.xtext.example.dJ.Expression;
import org.xtext.example.dJ.Field;
import org.xtext.example.dJ.MethodBody;
import org.xtext.example.dJ.ModifiesClass;
import org.xtext.example.dJ.Module;
import org.xtext.example.dJ.Parameter;
import org.xtext.example.dJ.Program;
import org.xtext.example.dJ.util.DJSwitch;

public class ContainingProgramFinded extends DJSwitch<Program>
{
	public Program lookup(Module m)
	  {
		EObject current = m;
	    EObject owner = null;
	    while (owner == null) {
	    	if(current == null) return null;
	      current = current.eContainer();
	      owner = (EObject)doSwitch(current);
	    }
	    return (Program)owner;
	  }
	public Program lookup(Argument m)
	  {
		EObject current = m;
	    EObject owner = null;
	    while (owner == null) {
	    	if(current == null) return null;
	      current = current.eContainer();
	      owner = (EObject)doSwitch(current);
	    }
	    return (Program)owner;
	  }
	public Program lookup(Parameter m)
	  {
		EObject current = m;
	    EObject owner = null;
	    while (owner == null) {
	    	if(current == null) return null;
	      current = current.eContainer();
	      owner = (EObject)doSwitch(current);
	    }
	    return (Program)owner;
	  }
	public Program lookup(Field m)
	  {
	    EObject current = m;
	    EObject owner = null;
	    while (owner == null) {
	      current = current.eContainer();
	      owner = (EObject)doSwitch(current);
	    }
	    return (Program)owner;
	  }	
	public Program lookup(Class m)
	  {
		    EObject current = m;
		    EObject owner = null;
		    while (owner == null) {
		      current = current.eContainer();
		      owner = (EObject)doSwitch(current);
		    }
		    return (Program)owner;
		  }
	public Program lookup(MethodBody m)
	  {
	    EObject current = m;
	    EObject owner = null;
	    while (owner == null) {
	      current = current.eContainer();
	      owner = (EObject)doSwitch(current);
	    }
	    return (Program)owner;
	  }
	public Program lookup(ModifiesClass m)
	  {
	    EObject current = m;
	    EObject owner = null;
	    while (owner == null) {
	      current = current.eContainer();
	      owner = (EObject)doSwitch(current);
	    }
	    return (Program)owner;
	  }
  public Program lookup(Constructor c)
  {
    EObject current = c;
    EObject owner = null;
    while (owner == null) {
      current = current.eContainer();
      owner = (EObject)doSwitch(current);
	    if (current == null) return null;
    }

    return (Program)owner;
  }
  public Program lookup(Expression c)
  {
    EObject current = c;
    EObject owner = null;
    while (owner == null) {
      current = current.eContainer();
      owner = (EObject)doSwitch(current);
	    if (current == null) return null;
    }

    return (Program)owner;
  }
  public Program caseProgram(Program program) {
    return program;
  }
}