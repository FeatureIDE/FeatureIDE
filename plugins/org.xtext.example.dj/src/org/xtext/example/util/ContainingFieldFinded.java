package org.xtext.example.util;

import org.eclipse.emf.ecore.EObject;
import org.xtext.example.dJ.Field;
import org.xtext.example.dJ.FieldRef;
import org.xtext.example.dJ.Module;
import org.xtext.example.dJ.util.DJSwitch;

public class ContainingFieldFinded extends DJSwitch<Field> {
	private boolean end = false;

	  public Field lookup(FieldRef e) { EObject current = e;
	    EObject owner = null;
	    while ((owner == null) && (!this.end)) {
	      current = current.eContainer();
	      owner = doSwitch(current);
	    }

	    return (Field)owner; 
	  }
	  
	  public Field caseField(Field field)
	  {
	    return field;
	  }
	  
	  public Field caseModule(Module module) {
	    this.end = true;
	    return null;
	  }
}
