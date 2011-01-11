package org.xtext.example.scoping;

import java.util.*;
import org.eclipse.emf.ecore.EReference;
import org.eclipse.emf.ecore.resource.Resource;
import org.eclipse.xtext.EcoreUtil2;
import org.eclipse.xtext.scoping.IScope;
import org.eclipse.xtext.scoping.Scopes;
import org.eclipse.xtext.scoping.impl.AbstractDeclarativeScopeProvider;
import org.xtext.example.linking.DjResourceFactory;
import org.xtext.example.lookup.AuxiliaryFunctions;
import org.xtext.example.dJ.*;
import org.xtext.example.dJ.Class;
import org.xtext.example.type.CheckReturnType;
import org.xtext.example.type.ClassType;
import org.xtext.example.util.*;

public class DJScopeProvider extends AbstractDeclarativeScopeProvider
{
  AuxiliaryFunctions auxiliaryFunctions = new AuxiliaryFunctions();

  public IScope scope_Feature(Delta d, EReference ref){
		Program p = new ContainingProgramFinded().lookup((Module)d.eContainer());
	    Collection<Import> importList = p.getImports();
	    Collection<Feature> featuresList = new LinkedList<Feature>();
	    if(p.getFeatures() != null){
	    	return Scopes.scopeFor(p.getFeatures().getFeaturesList());
	    }
	    for (Import imp : importList) {
	      Resource resource = EcoreUtil2.getResource(p.eResource(), imp.getImportURI());
	      if(resource.getContents().size() != 0){
	    	  Program current = (Program)resource.getContents().get(0);
	    	  if(current.getFeatures() != null)
	    		  featuresList.addAll(current.getFeatures().getFeaturesList());
	      }
	    }
	    return Scopes.scopeFor(featuresList);
	  }
  public IScope scope_Feature(Core c, EReference ref){
		Program p = new ContainingProgramFinded().lookup((Module)c.eContainer());
	    Collection<Import> importList = p.getImports();
	    Collection<Feature> featuresList = new LinkedList<Feature>();
	    if(p.getFeatures() != null){
	    	return Scopes.scopeFor(p.getFeatures().getFeaturesList());
	    }
	    for (Import imp : importList) {
	      Resource resource = EcoreUtil2.getResource(p.eResource(), imp.getImportURI());
	      if(resource.getContents().size() != 0){
	    	  Program current = (Program)resource.getContents().get(0);
	    	  if(current.getFeatures() != null)
	    		  featuresList.addAll(current.getFeatures().getFeaturesList());
	      }
	    }
	    return Scopes.scopeFor(featuresList);
	  }

  public IScope scope_Delta(Program p, EReference ref) {
    Collection<Import> importList = p.getImports();
    Collection<Module> moduleList = new LinkedList<Module>();
    Collection<Delta> deltaList = new LinkedList<Delta>();
    moduleList.addAll(p.getModulesList());
    for (Import imp : importList) {
      Resource resource = EcoreUtil2.getResource(p.eResource(), imp.getImportURI());
      if(resource.getContents().size() != 0){
    	  Program current = (Program)resource.getContents().get(0);
    	  moduleList.addAll(current.getModulesList());
      }
    }
    for (Module m : moduleList)
      if(m.getNtype() != null)	
      if (m.getNtype().equals("delta"))
        deltaList.add(m.getDelta());
    return Scopes.scopeFor(deltaList);
  }

  public IScope scope_Class(Field field, EReference ref){
	  Program p = new ContainingProgramFinded().lookup(field);
	  Collection<Class> classList = new LinkedList<Class>();
	    Collection<Import> importList = p.getImports();
	    Collection<Module> moduleList = new LinkedList<Module>();
	    moduleList.addAll(p.getModulesList());
	    Program current;
	    for (Import imp : importList) {
	      Resource resource = EcoreUtil2.getResource(p.eResource(), imp.getImportURI());
	      current = (Program)resource.getContents().get(0);
	      moduleList.addAll(current.getModulesList());
	    }
	    for (Module m : moduleList) {
	      if(m.getNtype() != null){
	    	  if (m.getNtype().equals("core")) {
	    		  classList.addAll(this.auxiliaryFunctions.coreClasses(m));
	    	  }
	    	  else if (m.getNtype().equals("delta")) {
	    		  for (Classm c : m.getDelta().getClassesList()) {
	    			  if (c.getAction().equals("adds")) {
	    				  classList.add(c.getAdds().getClass_());
	    			  }
	    		  }

	    	  }
	      }
	    }
	    Program p2 = (Program)DjResourceFactory.getSystemResource().getContents().get(0);
		for(Class cl : p2.getModulesList().get(0).getCore().getClassesList())
			if(!"SystemOutWrapper".equals(cl.getName()) && !"MyMath".equals(cl.getName()) && !"AllObject".equals(cl.getName()) )
				classList.add(cl);
		return Scopes.scopeFor(classList);
  }
  public IScope scope_Class(Program p, EReference ref) {
	    Collection<Class> classList = new LinkedList<Class>();
	    Collection<Import> importList = p.getImports();
	    Collection<Module> moduleList = new LinkedList<Module>();
	    moduleList.addAll(p.getModulesList());
	    Program current;
	    for (Import imp : importList) {
	      Resource resource = EcoreUtil2.getResource(p.eResource(), imp.getImportURI());
	      current = (Program)resource.getContents().get(0);
	      moduleList.addAll(current.getModulesList());
	    }
	    for (Module m : moduleList) {
	      if(m.getNtype() != null){
	    	  if (m.getNtype().equals("core")) {
	    		  classList.addAll(this.auxiliaryFunctions.coreClasses(m));
	    	  }
	    	  else if (m.getNtype().equals("delta")) {
	    		  for (Classm c : m.getDelta().getClassesList()) {
	    			  if (c.getAction().equals("adds")) {
	    				  classList.add(c.getAdds().getClass_());
	    			  }
	    		  }

	    	  }
	      }
	    }
	    Program p2 = (Program)DjResourceFactory.getSystemResource().getContents().get(0);
		for(Class cl : p2.getModulesList().get(0).getCore().getClassesList())
			if(!"AllObject".equals(cl.getName()))
				classList.add(cl);
		return Scopes.scopeFor(classList);
	  }
  public IScope scope_Class(Parameter par, EReference ref) {
	  	Module modTemp = new ContainingModuleFinded().lookup(par);
	  	Program p = new ContainingProgramFinded().lookup(modTemp);
	    Collection<Class> classList = new LinkedList<Class>();
	    Collection<Import> importList = p.getImports();
	    Collection<Module> moduleList = new LinkedList<Module>();
	    moduleList.addAll(p.getModulesList());
	    Program current;
	    for (Import imp : importList) {
	      Resource resource = EcoreUtil2.getResource(p.eResource(), imp.getImportURI());
	      current = (Program)resource.getContents().get(0);
	      moduleList.addAll(current.getModulesList());
	    }
	    for (Module m : moduleList) {
	      if(m.getNtype() != null){
	    	  if (m.getNtype().equals("core")) {
	    		  classList.addAll(this.auxiliaryFunctions.coreClasses(m));
	    	  }
	    	  else if (m.getNtype().equals("delta")) {
	    		  for (Classm c : m.getDelta().getClassesList()) {
	    			  if (c.getAction().equals("adds")) {
	    				  classList.add(c.getAdds().getClass_());
	    			  }
	    		  }

	    	  }
	      }
	    }
	    Program p2 = (Program)DjResourceFactory.getSystemResource().getContents().get(0);
	    for(Class cl : p2.getModulesList().get(0).getCore().getClassesList())
			if(!"AllObject".equals(cl.getName()))
				classList.add(cl);
		return Scopes.scopeFor(classList);
	  }
  public IScope scope_Class(Constructor constructor, EReference ref) {
    Collection<Class> c = new LinkedList<Class>();
    if (new ContainingClassFinded().lookup(constructor) != null)
      c.add(new ContainingClassFinded().lookup(constructor));
    if (c.isEmpty()) {
      Classm temp2 = new ContainingClassmFinded().lookup(constructor);
      if (temp2.getAction().equals("adds"))
        c.add(temp2.getAdds().getClass_());
      else
        c.add(temp2.getModifies().getClass_());
    }
    return Scopes.scopeFor(c);
  }

  public IScope scope_MethodRef(Classm cl, EReference ref)
  {
    Collection<MethodRef> methodRefList = new AuxiliaryFunctions().ricorsivo_MethodRef(cl);
    return Scopes.scopeFor(methodRefList);
  }

  public IScope scope_MethodRef(MethodCall mc, EReference ref) {
	  Collection<MethodRef> methodRefList = new LinkedList<MethodRef>();
	  Expression expression = new ContainingExpressionFinded().lookup(mc);
	  Expression receiver = expression.getReceiver();
	  ClassType ctTemp = new CheckReturnType().returnTypeMessage(receiver);
	  Class c = null;
	  c = ctTemp.getClassType();
	  if (c == null) {
		  return Scopes.scopeFor(methodRefList);
	  }
	  Module m = new ContainingModuleFinded().lookup(c);
	  Program p = new ContainingProgramFinded().lookup(m);
	  Collection<Import> importList = p.getImports();
	  Collection<Module> moduleList = new LinkedList<Module>();
	  moduleList.addAll(p.getModulesList());
	  for (Import imp : importList) {
		  Resource resource = EcoreUtil2.getResource(p.eResource(), imp.getImportURI());
		  if(resource.getContents().size() != 0){
			  Program current = (Program)resource.getContents().get(0);
			  moduleList.addAll(current.getModulesList());
		  }
	  }
	  Classm classm = null;
	  for (Module mod : moduleList)
		  if(mod.getNtype() != null)
			  if (mod.getNtype().equals("delta")) {
				  for (Classm cm : mod.getDelta().getClassesList()){
					  if (cm.getAction().equals("adds") &&
							  (cm.getAdds().getClass_().getName().equals(c.getName()))){
						  classm = cm;
					  }	
					  if ((cm.getAction().equals("modifies")) && 
							  (cm.getModifies().getClass_().getName().equals(c.getName()))){
						  classm = cm;
					  }
				  }
			  } 
	  if (classm != null) {
		  methodRefList = new AuxiliaryFunctions().ricorsivo_MethodRef(classm);
	  }
	  else {
		  Set<String> classes = new HashSet<String>();
		  for (Method method : c.getMethod()){
			  methodRefList.add(method.getReference());
		  }
		  classes.add(c.getName());
		  while ((c.getExtends() != null) && (classes.add(c.getExtends().getName()))) {
			  c = c.getExtends();
			  for (Method method : c.getMethod())
				  methodRefList.add(method.getReference());
		  }
	  }
	  return (IScope)Scopes.scopeFor(methodRefList);
  }

  public IScope scope_FieldRef(Classm cl, EReference ref)
  {
    Collection<FieldRef> fieldRefList = new AuxiliaryFunctions().ricorsivo_FieldRef(cl);
    return Scopes.scopeFor(fieldRefList);
  }

  public IScope scope_FieldRef(Constructor cons, EReference ref)
  {
	try{
    Collection<FieldRef> fieldRefList = new LinkedList<FieldRef>();

    Classm cm = new ContainingClassmFinded().lookup(cons);
    if (cm != null) {
      fieldRefList = new AuxiliaryFunctions().ricorsivo_FieldRef(cm);
    } else {
      Class c = new ContainingClassFinded().lookup(cons);
      if (c != null) {
        for (Field f : c.getField())
          fieldRefList.add(f.getReference());
      }
    }
    if(fieldRefList != null)
    	return Scopes.scopeFor(fieldRefList);
    return null;
	}catch(Exception ex) {ex.printStackTrace(); return null;}
  }

  public IScope scope_FieldRef(Variable var, EReference ref) {
    Collection<FieldRef> fieldRefList = new LinkedList<FieldRef>();
    Classm cm = new ContainingClassmFinded().lookup((TerminalExpression)var.eContainer());
    if (cm != null) {
      fieldRefList = new AuxiliaryFunctions().ricorsivo_FieldRef(cm);
    } else {
      Class c = new ContainingClassFinded().lookup((TerminalExpression)var.eContainer());
      if (c != null)
        for (Field f : c.getField())
          fieldRefList.add(f.getReference());
    }
    return Scopes.scopeFor(fieldRefList);
  }

  public IScope scope_FieldRef(FieldAccess fa, EReference ref) {
    Collection<FieldRef> fieldRefList = new LinkedList<FieldRef>();
    Expression expression = new ContainingExpressionFinded().lookup(fa);
    Class c = null;
    c = new CheckReturnType().returnTypeMessage(expression.getReceiver()).getClassType();
    if (c == null) {
      return Scopes.scopeFor(fieldRefList);
    }
    Module m = new ContainingModuleFinded().lookup(c);
    Program p = new ContainingProgramFinded().lookup(m);
    Collection<Import> importList = p.getImports();
    Collection<Module> moduleList = new LinkedList<Module>();
    moduleList.addAll(p.getModulesList());
    for (Import imp : importList) {
      Resource resource = EcoreUtil2.getResource(p.eResource(), imp.getImportURI());
      if(resource.getContents().size() != 0){
    	  Program current = (Program)resource.getContents().get(0);
    	  moduleList.addAll(current.getModulesList());
      }
    }
    Classm classm = null;
    for (Module mod : moduleList)
      if(mod.getNtype() != null)
      if (mod.getNtype().equals("delta"))
        for (Classm cm : mod.getDelta().getClassesList())
          if (cm.getAction().equals("adds")) {
            if (cm.getAdds().getClass_().getName().equals(c.getName()))
              classm = cm;
          }
          else {
            if ((cm.getAction().equals("modifies")) && 
              (c.getName().equals(cm.getModifies().getClass_().getName())))
            classm = cm;
          }

    if (classm != null) {
      fieldRefList = new AuxiliaryFunctions().ricorsivo_FieldRef(classm);
    }
    else {
      Set<String> classes = new HashSet<String>();

      for (Field f : c.getField())
        fieldRefList.add(f.getReference());
      classes.add(c.getName());

      while ((c.getExtends() != null) && (classes.add(c.getExtends().getName()))) {
        c = c.getExtends();
        for (Field f : c.getField())
          fieldRefList.add(f.getReference());
      }
    }
    return (IScope)Scopes.scopeFor(fieldRefList);
  }

  public IScope scope_Class(Core c, EReference reference) {
		List<Class> classList = new LinkedList<Class>();
		Program p = (Program)DjResourceFactory.getSystemResource().getContents().get(0);
		for(Class cl : p.getModulesList().get(0).getCore().getClassesList())
			if(!"AllObject".equals(cl.getName()))
				classList.add(cl);
		classList.addAll(c.getClassesList());
	    return Scopes.scopeFor(classList);
  }
}