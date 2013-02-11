package org.xtext.example.type;

import java.util.Collection;
import java.util.HashSet;
import java.util.LinkedList;

import org.eclipse.emf.ecore.resource.Resource;
import org.eclipse.xtext.EcoreUtil2;
import org.xtext.example.dJ.AddsField;
import org.xtext.example.dJ.AddsMethod;
import org.xtext.example.dJ.Class;
import org.xtext.example.dJ.Classm;
import org.xtext.example.dJ.Expression;
import org.xtext.example.dJ.Field;
import org.xtext.example.dJ.Import;
import org.xtext.example.dJ.Method;
import org.xtext.example.dJ.ModifiesMethod;
import org.xtext.example.dJ.Module;
import org.xtext.example.dJ.Program;
import org.xtext.example.dJ.TerminalExpression;
import org.xtext.example.dJ.Type;
import org.xtext.example.linking.DjResourceFactory;
import org.xtext.example.util.ContainingClassFinded;
import org.xtext.example.util.ContainingClassmFinded;
import org.xtext.example.util.ContainingModifiesMethodFinded;
import org.xtext.example.util.ContainingModuleFinded;
import org.xtext.example.util.ContainingProgramFinded;

public class CheckReturnType {
	
	/*
	 * Ritorna il tipo dell'espressione di partenza che per˜ ho chiamato TerminalExpression
	 * guardare poi la classe ClassType
	 */
	public ClassType returnTypeTerminalExpression(TerminalExpression te){
		ClassType ct = new ClassType();
		if(te.getCast() != null) {
			ct.setClass(te.getCast().getType());
			return (ct);
		}
		else if (te.getNew() != null) {
			ct.setClass(te.getNew().getType());
			return (ct);
		}	
		else if (te.getThis() != null) {
			Class c = new ContainingClassFinded().lookup(te);
			if (c == null){
				Classm cm = new ContainingClassmFinded().lookup(te);
				if(cm.getAction().equals("adds"))
					c = cm.getAdds().getClass_();
				else
					c = cm.getModifies().getClass_();
			}
			ct.setClass(c);
			return (ct);
		} else if (te.getVariable() != null) {
			Type t = null;
			if (te.getVariable().getParameter() != null) {
				t = te.getVariable().getParameter().getType();
			} else {
				String name = te.getVariable().getFieldRef().getName();
				Class tempClass2 = new ContainingClassFinded().lookup(te);
				if (tempClass2 == null) {
					Classm cm = new ContainingClassmFinded().lookup(te);
					if (cm.getAction().equals("adds"))
						tempClass2 = cm.getAdds().getClass_();
					else
						tempClass2 = cm.getModifies().getClass_();
				}
				t = checkTypeField(name, tempClass2);
			}
			ct.setType(t);
			return ct;
		}
		else if (te.getOriginal() != null) {
			ModifiesMethod mm = new ContainingModifiesMethodFinded().lookup(te.getOriginal());
			if (mm != null)
				ct.setType(mm.getReturntype());
			return ct;
		}
		else if (te.getString() != null){
			Program p = (Program)DjResourceFactory.getSystemResource().getContents().get(0);
			for(Class classes : (p.getModulesList().get(0).getCore().getClassesList()))
				if(classes.getName().equals("String")){
					ct.setClass(classes);
					break;
				}
		}
		else if (te.getInt() != null)
			ct.setBasic("int");
		else if (te.getNull() != null)
			ct.setBasic("null");
		return ct;
	}
	
	/*
	 * Ritorna il tipo dell'espressione passata come parametro guardare poi la classe ClassType 
	 */
	public ClassType returnTypeMessage(Expression ex){
	    ClassType ct = new ClassType();
	    if(ex.getReceiver() == null && ex.getTerminalExpression() != null)
	    	return returnTypeTerminalExpression(ex.getTerminalExpression());
	    if (ex.getReceiver().getTerminalExpression() == null) {
	      ct = returnTypeMessage(ex.getReceiver());
	    }
	    else if (ex.getReceiver().getTerminalExpression()!= null) {
	    	ct = returnTypeTerminalExpression(ex.getReceiver().getTerminalExpression());
	    }
	    ClassType classType = new ClassType();
        if(ex.getMessage() != null)
	    if (ex.getMessage().getFieldAccess() != null) {
	      if (ct != null) {
	    	  if (ct.getClassType() != null) {
	    		  Type typetemp = checkTypeField(ex.getMessage().getFieldAccess().getName().getName(), ct.getClassType());
	    		  if (typetemp != null){
	    			  classType.setType(typetemp);
	    			  return classType;
	    		  }
	    	  }
	      }
	    }
	    else if (ex.getMessage().getMethodCall() != null) {
	      if (ct != null) {
	        if (ct.getClassType() != null) {
	          Type typetemp = checkTypeMethod(ex.getMessage().getMethodCall().getName().getName(), ct.getClassType());
	          if (typetemp != null){
	              classType.setType(typetemp);
	              return classType;
	          }
	        }
	      }
	    }
	    return classType;
	  }
	private Type checkTypeMethod(String name, Class cl) {
		Collection<Module> moduleList = new HashSet<Module>();
		Type type = null;	
	    Collection<Class> parentClasses = new LinkedList<Class>();
	    Module module = new ContainingModuleFinded().lookup(cl);
	    Program p = new ContainingProgramFinded().lookup(module);
	    
	    Collection<Import> importList = new HashSet<Import>();
	    if(p != null){
	    	importList = p.getImports();
	    	moduleList.addAll(p.getModulesList());
	    }
	    Program current;
	    for (Import imp : importList) {
	      if(imp != null && p != null && p.eResource() != null && imp.getImportURI() != null){
	    	  Resource resource = EcoreUtil2.getResource(p.eResource(), imp.getImportURI());
	    	  current = (Program)resource.getContents().get(0);
	    	  moduleList.addAll(current.getModulesList());
	      }
	    }
	    for (Module mod : moduleList) {
	      if(mod.getNtype() == null){
	    	  Program p2 = (Program)DjResourceFactory.getSystemResource().getContents().get(0);
	    	  for(Class c : p2.getModulesList().get(0).getCore().getClassesList())
	    		  if (c.getName().equals(cl.getName())) {
	    	            if (c.getExtends() != null) parentClasses.add(c.getExtends());
	    	            for (Method method : c.getMethod())
	    	              if (method.getReference().getName().equals(name))
	    	                return method.getReturntype();
	    	          }
	      }
	      else
	      if (mod.getNtype().equals("core")){
	        for (Class c : mod.getCore().getClassesList())
	          if (c.getName().equals(cl.getName())) {
	            for (Method method : c.getMethod())
	              if (method.getReference().getName().equals(name))
	                return method.getReturntype();
	            if (c.getExtends() != null) 
	            	parentClasses.add(c.getExtends());
	          }
	      }else {
	        for (Classm cm : mod.getDelta().getClassesList()) {
	          if (cm.getAction().equals("adds")) {
	            if (cm.getAdds().getClass_().getName().equals(cl.getName())) {
	              for (Method method : cm.getAdds().getClass_().getMethod())
	                if (method.getReference().getName().equals(name))
	                  return method.getReturntype(); 
	              if (cm.getAdds().getClass_().getExtends() != null) 
	            	  parentClasses.add(cm.getAdds().getClass_().getExtends());
	             }
	          } else {
	        	  //FIX ME XTEXT null-checks added
	        	  if ((cm != null && cm.getAction() != null && cm.getAction().equals("modifies")) &&
	        			  (cm.getModifies() != null && cm.getModifies().getClass_() != null &&
	        			   cm.getModifies().getClass_().getName() != null && cm.getModifies().getClass_().getName().equals(cl.getName()))){
	        		  for (AddsMethod amethod : cm.getModifies().getMethod().getAddsList())
	        			  if (amethod.getMethod().getReference().getName().equals(name))
	        				  return amethod.getMethod().getReturntype();
	        		  if (cm.getModifies().getExtends() != null)
	        			  parentClasses.add(cm.getModifies().getExtends());
	        	  }
	          }
	        }
	      }
	    }
	    for (Class pclass : parentClasses) {
	      type = checkTypeMethod(name, pclass);
	      if (type != null)
	        return type;
	    }
	    return null;
	}	
	public Type checkTypeField(String name, Class cl) {	
		Collection<Module> moduleList = new LinkedList<Module>();
		Collection<Class> parentClasses = new HashSet<Class>();
		Module module = null;
		Program p = null;
		Type type = null;
		if(name == null || cl == null || cl.getName().equals("") ) return null;
		module = new ContainingModuleFinded().lookup(cl);
		p = new ContainingProgramFinded().lookup(module);
		Collection<Import> importList = null;
		if(p != null){
			importList = p.getImports();
			moduleList.addAll(p.getModulesList());
			Program current;
			//FIX ME XTEXT
			for (Import imp : importList) {
				if(p.eResource() == null) continue; // NEW
				Resource resource = EcoreUtil2.getResource(p.eResource(), imp.getImportURI());
				current = (Program)resource.getContents().get(0);
				moduleList.addAll(current.getModulesList());
			}
			for (Module mod : moduleList) {
				if (mod.getNtype() != null)
					if (mod.getNtype().equals("core")){
						for (Class c : mod.getCore().getClassesList())
							if (c.getName().equals(cl.getName())) {
								for (Field f : c.getField())
									if (f.getReference().getName().equals(name))
										return f.getType();
								if (c.getExtends() != null)
									parentClasses.add(c.getExtends());
							}
					}else {
						for (Classm cm : mod.getDelta().getClassesList()) {
							if (cm.getAction().equals("adds")) {
								if (cm.getAdds().getClass_().getName().equals(cl.getName())) {
									for (Field f : cm.getAdds().getClass_().getField())
										if (f.getReference().getName().equals(name))
											return f.getType(); 
									if (cm.getAdds().getClass_().getExtends() != null) 
										parentClasses.add(cm.getAdds().getClass_().getExtends());
								}
							} else {
								if ((cm != null && cm.getAction() != null && cm.getAction().equals("modifies")) &&
										(cm.getModifies() != null && cm.getModifies().getClass_() != null && 
										 cm.getModifies().getClass_().getName() != null &
										 cl != null && cl.getName() != null && cm.getModifies().getClass_().getName().equals(cl.getName()))){
									for (AddsField af : cm.getModifies().getField().getAddsList())
										if (af.getField().getReference().getName().equals(name))
											return af.getField().getType();
									if (cm.getModifies().getExtends() != null) 
										parentClasses.add(cm.getModifies().getExtends());
								}
							}
						}
					}
			}
	    }
		for (Class pclass : parentClasses) {
	      type = checkTypeField(name, pclass);
	      if (type != null)
	        return type;
	    }
	    return null;
	  }

	 public boolean isFinal(Expression ex){
		 ClassType ct = returnTypeMessage(ex);
		 if(ct.getBasicType() != null) return false;
		 else{
			 Program p = (Program)DjResourceFactory.getSystemResource().getContents().get(0);
			 for(Class c : (p.getModulesList().get(0).getCore().getClassesList())){
				 if(c.getName().equals(ct.getClassType().getName())) return true;
			 }
		 }
		 return false;
	 }
	  
}
