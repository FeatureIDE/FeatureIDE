package org.xtext.example.lookup;

import java.math.BigInteger;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Map;
import java.util.Set;

import org.eclipse.emf.ecore.resource.Resource;
import org.eclipse.xtext.EcoreUtil2;
import org.xtext.example.dJ.AddsField;
import org.xtext.example.dJ.AddsMethod;
import org.xtext.example.dJ.Class;
import org.xtext.example.dJ.Classm;
import org.xtext.example.dJ.Condition;
import org.xtext.example.dJ.Config;
import org.xtext.example.dJ.Constructor;
import org.xtext.example.dJ.Core;
import org.xtext.example.dJ.DJFactory;
import org.xtext.example.dJ.Delta;
import org.xtext.example.dJ.Feature;
import org.xtext.example.dJ.Field;
import org.xtext.example.dJ.FieldRef;
import org.xtext.example.dJ.Import;
import org.xtext.example.dJ.Method;
import org.xtext.example.dJ.MethodBody;
import org.xtext.example.dJ.MethodRef;
import org.xtext.example.dJ.ModifiesClass;
import org.xtext.example.dJ.Module;
import org.xtext.example.dJ.Program;
import org.xtext.example.linking.DjResourceFactory;
import org.xtext.example.util.ACST;
import org.xtext.example.util.CST;
import org.xtext.example.util.ContainingModuleFinded;
import org.xtext.example.util.ContainingProgramFinded;

public class AuxiliaryFunctions
{
  Program program;

  // return true if the after clauses are cyclic.
  public boolean cyclicAfter(Delta d, HashSet<String> deltaAfter){
	  deltaAfter.add(d.getName());
	  try{
		  for (Delta dAfter : d.getAfter()) {
			  if (!deltaAfter.add(dAfter.getName())) {
				  return true;
			  }
			  if (!cyclicAfter(dAfter, deltaAfter))
				  deltaAfter.remove(dAfter.getName());
			  else {
				  return true;
			  }
		  }
	  }catch (java.lang.AssertionError ex) {  	
		  ex.printStackTrace();
		  return true;
	  }
	  return false;
  }
  
  // return the set of ModifiesClass present in all delta "after" of d of a modifiesClass of d
  public Set<ModifiesClass> modifiedClassesAfter(Delta d, ModifiesClass modifies) {
    if (cyclicAfter(d, new HashSet<String>())) return null;
    Collection<Classm> classmList = new LinkedList<Classm>();
    Set<ModifiesClass> modifiesList = new HashSet<ModifiesClass>();
    classmList.addAll(d.getClassesList());
    for (Classm c : classmList) {
      if (c.getAction().equals("modifies") && c.getModifies().getClass_().equals(modifies.getClass_()))
    	  modifiesList.add(c.getModifies());
    }for (Delta dAfter : d.getAfter())
      modifiesList.addAll(modifiedClassesAfter(dAfter, modifies));
    return modifiesList;
  }

  public Classm lookClassExtend(Delta d, String s)
  {
    if (cyclicAfter(d, new HashSet<String>())) return null;
    Classm classm = null;
    BigInteger level = new BigInteger("-1");
    Program p = new ContainingProgramFinded().lookup((Module)d.eContainer());
    Collection<Classm> classmList = new LinkedList<Classm>();
    classmList.addAll(d.getClassesList());
    for (Classm c : classmList) {
      if ((c.getAction().equals("modifies")) && 
        (c.getModifies().getClass_().getName().equals(s)))
        return c;
      if ((c.getAction().equals("adds")) && 
        (c.getAdds().getClass_().getName().equals(s)))
        return c; 
    }
    Map<BigInteger, Set<Delta>> deltaLevel = allDeltaLevel(p);
    for (BigInteger b : deltaLevel.keySet()) {
      level = b;
    }

    while (level.compareTo(BigInteger.ZERO) != 0) {
      for (Delta delta : deltaLevel.get(level)) {
        classmList.clear();
        classmList.addAll(delta.getClassesList());
        for (Classm c : classmList) {
          if ((c.getAction().equals("modifies")) && 
            (c.getModifies().getClass_().getName().equals(s)))
            return c;
          if ((c.getAction().equals("adds")) && 
            (c.getAdds().getClass_().getName().equals(s)))
            return c; 
        }
      }
      level = level.subtract(BigInteger.ONE);
    }

    return classm;
  }

  public Collection<Class> coreClasses(Module m) {
    Collection<Class> classList = new LinkedList<Class>();
    Collection<Import> importList = new LinkedList<Import>();
    Collection<Core> coreList = new LinkedList<Core>();
    Program p = new ContainingProgramFinded().lookup(m);
    importList.addAll(p.getImports());
    for (Import imp : importList) {
      Resource resource = EcoreUtil2.getResource(p.eResource(), imp.getImportURI());
      if(resource.getContents().size() != 0){
    	  Program current = (Program)resource.getContents().get(0);
    	  for (Module module : current.getModulesList())
    		  if(module.getNtype() != null)
    			  if (module.getNtype().equals("core"))
    				  coreList.add(module.getCore());
      }
    }
    for (Module mod : p.getModulesList())
      if(mod.getNtype() != null)
    	  if (mod.getNtype().equals("core"))
    		  coreList.add(mod.getCore());
    for (Core c : coreList)
      classList.addAll(c.getClassesList());
    return classList;
  }

  public Map<BigInteger, Set<Delta>> allDeltaLevel(Program p) {
    
	return deltaLevel(p, null);
  }

  public Map<BigInteger, Set<Delta>> deltaLevel(Program p, Config config) {
    Map<BigInteger, Set<Delta>> deltaMapLevel = new HashMap<BigInteger, Set<Delta>>();
    Collection<Import> importList = new LinkedList<Import>();
    Collection<Delta> deltaList = new LinkedList<Delta>();
    Collection<Delta> deltaDelete = new LinkedList<Delta>();
    Collection<Delta> deltaTemp = new LinkedList<Delta>();
    importList.addAll(p.getImports());
    for (Module module : p.getModulesList())
      if(module.getNtype() != null)
      if (module.getNtype().equals("delta"))
        deltaTemp.add(module.getDelta());
    for (Import imp : importList) {
      Resource resource = EcoreUtil2.getResource(p.eResource(), imp.getImportURI());
      if(resource!=null&&resource.getContents().size() != 0){
    	  Program current = (Program)resource.getContents().get(0);
    	  for (Module module : current.getModulesList())
    		  if(module.getNtype() != null)
    			  if (module.getNtype().equals("delta"))
    				  deltaTemp.add(module.getDelta()); 
      }
    }
    for (Delta d : deltaTemp) {
      boolean valid = true;
      for (Condition c : d.getCondition())
        if (config != null && !validDeltaWhen(c, config))
          valid = false;
      if (valid)
        deltaList.add(d);
      else {
        deltaDelete.add(d);
      }
    }
    for (Delta d : deltaList) {
      Set<Delta> deltas = new HashSet<Delta>();
      BigInteger level = deltaLevel(d, deltaDelete);
      if (level.compareTo(new BigInteger("-1")) != 0) {
        if (deltaMapLevel.get(level) != null)
          deltas.addAll(deltaMapLevel.get(level));
        deltas.add(d);
        deltaMapLevel.put(level, deltas);
      }
    }
    return deltaMapLevel;
  }
  
  //return if two class are in a cyclic inheritance for example A extends B and B extends A
  public boolean cyclicInheritance(String name, Map<String, ACST> mapClass) {
    Set<String> classExtending = new HashSet<String>();
    classExtending.addAll(mapClass.get(name).getExtending());
    for (String name2 : classExtending){
        if (mapClass.get(name2).getExtending().contains(name))
        return true;
    }
    return false;
  }
  
  public boolean isParentClass(String returnType, String methodReturnType, Map<String, CST> classApply) {
	  	String parent = null;
	    if (returnType != null && returnType.equals(methodReturnType))
	      return true;
	    if (returnType != null && classApply.get(returnType) != null)
	      parent = ((CST)classApply.get(returnType)).getExtending();
	    else
	      return false;
	    if ((parent != null) && (classApply.get(parent) != null)) {
	      return isParentClass(parent, methodReturnType, classApply);
	    }
	    return false;
	  }
  public Collection<MethodRef> ricorsivo_MethodRef(Classm cl)
  {
    Collection<Module> moduleList = new LinkedList<Module>();
    Collection<MethodRef> methodRefList = new LinkedList<MethodRef>();
    Module module = null;
    Program p = null;
    if (cl.getAction().equals("adds"))
      module = new ContainingModuleFinded().lookup(cl.getAdds());
    if (cl.getAction().equals("modifies"))
      module = new ContainingModuleFinded().lookup(cl.getModifies());
    p = new ContainingProgramFinded().lookup(module);
    if(p == null) return null;
    Collection<Import> importList = p.getImports();
    moduleList.addAll(p.getModulesList());
    Program current;
    for (Import imp : importList) {
      Resource resource = EcoreUtil2.getResource(p.eResource(), imp.getImportURI());
      current = (Program)resource.getContents().get(0);
      moduleList.addAll(current.getModulesList());
    }
    if (cl.getAction().equals("adds")) {
      for (Module m : moduleList) {
    	if(m.getNtype() != null)  
        if (m.getNtype().equals("core")) {
          for (Class c : coreClasses(m))
            if (c.getName().equals(cl.getAdds().getClass_().getName())) {
              for (Method method : c.getMethod())
                methodRefList.add(method.getReference());
              while (c.getExtends() != null) {
                c = c.getExtends();
                for (Method method : c.getMethod())
                  methodRefList.add(method.getReference());
              }
            }
        }
        else if (m.getNtype().equals("delta")) {
          for (Classm cm : m.getDelta().getClassesList()) {
            if ((cm.getAction().equals("adds")) && 
              (cm.getAdds().getClass_().getName().equals(cl.getAdds().getClass_().getName()))) {
              for (Method method : cm.getAdds().getClass_().getMethod())
                methodRefList.add(method.getReference()); 
            } else {
              if (cm.getAction().equals("modifies") && 
                (cm.getModifies().getClass_().getName().equals(cl.getAdds().getClass_().getName())))
              for (AddsMethod af : cm.getModifies().getMethod().getAddsList()) {
                methodRefList.add(af.getMethod().getReference());
              }

              Classm temp = cm;
              if (temp.getModifies().getExtends() != null) {
                temp = lookClassExtend((Delta)temp.eContainer(), temp.getModifies().getExtends().getName());
                if (temp == null) {
                  for (Method method : cm.getModifies().getExtends().getMethod())
                    methodRefList.add(method.getReference()); 
                  return methodRefList;
                }
                methodRefList.addAll(ricorsivo_MethodRef(temp));
              }
            }
          }
        }
      }
    }
    if (cl.getAction().equals("modifies")) {
      for (Module m : moduleList) {
        if(m.getNtype() != null)
        if (m.getNtype().equals("core")){
          for (Class c : coreClasses(m))
            if (c.getName().equals(cl.getModifies().getClass_().getName())) {
              for (Method method : c.getMethod())
                methodRefList.add(method.getReference()); 
              while (c.getExtends() != null) {
                c = c.getExtends();
                for (Method method : c.getMethod())
                  methodRefList.add(method.getReference());
              }
            }
        }else if (m.getNtype().equals("delta")) {
          for (Classm cm : m.getDelta().getClassesList()) {
            if ((cm.getAction().equals("adds")) && 
              (cm.getAdds().getClass_().getName().equals(cl.getModifies().getClass_().getName()))) {
              for (Method method : cm.getAdds().getClass_().getMethod())
                methodRefList.add(method.getReference()); 
            } else  if ((cm.getAction().equals("modifies")) &&
                (cm.getModifies().getClass_().getName().equals(cl.getModifies().getClass_().getName()))){
              for (AddsMethod am : cm.getModifies().getMethod().getAddsList())
            	  methodRefList.add(am.getMethod().getReference());
              Classm temp = cm;
              if (temp.getModifies().getExtends() != null) {
                temp = lookClassExtend((Delta)temp.eContainer(), temp.getModifies().getExtends().getName());
                if (temp == null) {
                  for (Method method : cm.getModifies().getExtends().getMethod())
                    methodRefList.add(method.getReference());
                  return methodRefList;
                }
                methodRefList.addAll(ricorsivo_MethodRef(temp));
              }
            }
          }
        }
      }
    }
    return methodRefList;
  }

  public Collection<FieldRef> ricorsivo_FieldRef(Classm cl)
  {
    Collection<Module> moduleList = new LinkedList<Module>();
    Collection<FieldRef> fieldRefList = new LinkedList<FieldRef>();
    Module module = null;
    Program p = null;
    if (cl.getAction().equals("adds"))
      module = new ContainingModuleFinded().lookup(cl.getAdds());
    if (cl.getAction().equals("modifies"))
      module = new ContainingModuleFinded().lookup(cl.getModifies());
    p = new ContainingProgramFinded().lookup(module);
    if(p == null) return null;
    Collection<Import> importList = p.getImports();
    moduleList.addAll(p.getModulesList());
    Program current;
    for (Import imp : importList) {
      Resource resource = EcoreUtil2.getResource(p.eResource(), imp.getImportURI());
      if(resource.getContents().size() > 0)
    	  current = (Program)resource.getContents().get(0);
      else break;
      moduleList.addAll(current.getModulesList());
    }
    if (cl.getAction().equals("adds")) {
      for (Module m : moduleList) {
        if(m.getNtype() != null)
        if (m.getNtype().equals("core")) {
          for (Class c : coreClasses(m))
            if (c.getName().equals(cl.getAdds().getClass_().getName())) {
              for (Field field : c.getField())
                fieldRefList.add(field.getReference());
              while (c.getExtends() != null) {
                c = c.getExtends();
                for (Field field : c.getField())
                  fieldRefList.add(field.getReference());
              }
            }
        }
        else if (m.getNtype().equals("delta")) {
          for (Classm cm : m.getDelta().getClassesList()) {
            if ((cm.getAction().equals("adds")) && 
              (cm.getAdds().getClass_().getName().equals(cl.getAdds().getClass_().getName()))) {
              for (Field field : cm.getAdds().getClass_().getField())
                fieldRefList.add(field.getReference()); 
              //FIX ME XTEXT null-checks added
            } else if ((cm.getAction().equals("modifies"))){
            	if(cm != null && cm.getModifies() != null &&
            	   cm.getModifies().getClass_() != null &&
            	   cm.getModifies().getClass_().getName() != null &&
            	   cl != null &&
            	   cl.getAdds() != null &&
            	   cl.getAdds().getClass_() != null &&
            	   cl.getAdds().getClass_().getName() != null &&
            	   cm.getModifies().getClass_().getName().equals(cl.getAdds().getClass_().getName())){
              for (AddsField af : cm.getModifies().getField().getAddsList()) {
                fieldRefList.add(af.getField().getReference());
              }
            	
              Classm temp = cm;
              if (temp.getModifies().getExtends() != null) {
                temp = lookClassExtend((Delta)temp.eContainer(), temp.getModifies().getExtends().getName());
                if (temp == null) {
                  for (Field field : cm.getModifies().getExtends().getField())
                    fieldRefList.add(field.getReference());
                  return fieldRefList;
                }
                fieldRefList.addAll(ricorsivo_FieldRef(temp));
              }
            }}
          }
        }
      }
    }

    if (cl.getAction().equals("modifies")) {
      for (Module m : moduleList) {
        if(m.getNtype() != null)
        if (m.getNtype().equals("core")){
          for (Class c : coreClasses(m))
            if (c.getName().equals(cl.getModifies().getClass_().getName())) {
              for (Field field : c.getField())
                fieldRefList.add(field.getReference());
              while (c.getExtends() != null) {
                c = c.getExtends();
                for (Field field : c.getField())
                  fieldRefList.add(field.getReference()); 

              }
            }
        }else if (m.getNtype().equals("delta")) {
          for (Classm cm : m.getDelta().getClassesList()) {
            if ((cm.getAction().equals("adds")) && 
              (cm.getAdds().getClass_().getName().equals(cl.getModifies().getClass_().getName()))) {
              for (Field field : cm.getAdds().getClass_().getField())
                fieldRefList.add(field.getReference()); 
            } else if ((cm.getAction().equals("modifies")) &&
                (cm.getModifies().getClass_().getName().equals(cl.getModifies().getClass_().getName()))){
              for (AddsField af : cm.getModifies().getField().getAddsList())
                fieldRefList.add(af.getField().getReference());
              Classm temp = cm;
              if (temp.getModifies().getExtends() != null) {
                temp = lookClassExtend((Delta)temp.eContainer(), temp.getModifies().getExtends().getName());
                if (temp == null) {
                  for (Field field : cm.getModifies().getExtends().getField())
                    fieldRefList.add(field.getReference());
                  return fieldRefList;
                }
                fieldRefList.addAll(ricorsivo_FieldRef(temp));
              }
            }
          }
        }
      }
    }

    return (Collection<FieldRef>)fieldRefList;
  }

 /* public ClassType checkType(Expression ex){
    ClassType ct = new ClassType();
    Type type = null;
    Type temp = null;
    Class tempClass = null;
    if (ex.getReceiver().getTerminalExpression() == null) {
      ct = checkType(ex.getReceiver());
    }
    else if (ex.getReceiver().getTerminalExpression().getCast() != null) {
      tempClass = ex.getReceiver().getTerminalExpression().getCast().getType();
    } else if (ex.getReceiver().getTerminalExpression().getNew() != null) {
      tempClass = ex.getReceiver().getTerminalExpression().getNew().getType();
    } else if (ex.getReceiver().getTerminalExpression().getThis() != null) {
    	tempClass = new ContainingClassFinded().lookup(ex.getReceiver().getTerminalExpression());
    	if (tempClass == null) {
    		Classm cm = new ContainingClassmFinded().lookup(ex.getReceiver().getTerminalExpression());
    		if (cm.getAction().equals("adds"))
    			tempClass = cm.getAdds().getClass_();
    		else
    			tempClass = cm.getModifies().getClass_();
    	}
    } else if (ex.getReceiver().getTerminalExpression().getVariable() != null) {
      if (ex.getReceiver().getTerminalExpression().getVariable().getParameter() != null) {
        temp = ex.getReceiver().getTerminalExpression().getVariable().getParameter().getType();
      } else {
        String name = ex.getReceiver().getTerminalExpression().getVariable().getFieldRef().getName();
        Class tempClass2 = new ContainingClassFinded().lookup(ex.getReceiver().getTerminalExpression());
        if (tempClass2 == null) {
          Classm cm = new ContainingClassmFinded().lookup(ex.getReceiver().getTerminalExpression());
          if (cm.getAction().equals("adds"))
            tempClass2 = cm.getAdds().getClass_();
          else
            tempClass2 = cm.getModifies().getClass_();
        }
        temp = checkTypeField(name, tempClass2);
      }
    } else if (ex.getReceiver().getTerminalExpression().getOriginal() != null) {
        ModifiesMethod originalMethod = new ContainingModifiesMethodFinded().lookup(ex.getReceiver().getTerminalExpression().getOriginal());
        if (originalMethod != null) {
          temp = originalMethod.getReturntype();
        }  
    } else if (ex.getReceiver().getTerminalExpression().getInt() != null) {
    	
    }
    if(ex.getMessage() != null)
    if (ex.getMessage().getFieldAccess() != null) {
      if (temp != null) {
        if (temp.getClassref() != null) {
          Type typetemp = checkTypeField(ex.getMessage().getFieldAccess().getName().getName(), temp.getClassref());
          if (typetemp != null){
            ct.setType(typetemp);
        	return ct;
          }
        }
      }
      else if (tempClass != null) {
        Type typetemp = checkTypeField(ex.getMessage().getFieldAccess().getName().getName(), tempClass);
        if (typetemp != null){
            ct.setType(typetemp);
        	return ct;
          }
      }
    }
    else if (ex.getMessage().getMethodCall() != null) {
      if (temp != null) {
        if (temp.getClassref() != null) {
          Type typetemp = checkTypeMethod(ex.getMessage().getMethodCall().getName().getName(), temp.getClassref());
          if (typetemp != null){
              ct.setType(typetemp);
          	return ct;
            }
        }
      }
      else if (tempClass != null) {
        Type typetemp = checkTypeMethod(ex.getMessage().getMethodCall().getName().getName(), tempClass);
        if (typetemp != null) {
            ct.setType(typetemp);
        	return ct;
          }
      }
    }
    return ct;
  }
  private Type checkTypeMethod(String name, Class cl) {
    Collection<Module> moduleList = new HashSet<Module>();
    Module module = null;
    Program p = null;
    Type type = null;
    Collection<Class> parentClasses = new LinkedList<Class>();
    module = new ContainingModuleFinded().lookup(cl);
    p = new ContainingProgramFinded().lookup(module);
    Collection<Import> importList = p.getImports();
    moduleList.addAll(p.getModulesList());
    Program current;
    for (Import imp : importList) {
      Resource resource = EcoreUtil2.getResource(p.eResource(), imp.getImportURI());
      current = (Program)resource.getContents().get(0);
      moduleList.addAll(current.getModulesList());
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
            if (c.getExtends() != null) parentClasses.add(c.getExtends());
            for (Method method : c.getMethod())
              if (method.getReference().getName().equals(name))
                return method.getReturntype();
          }
      }else {
        for (Classm cm : mod.getDelta().getClassesList()) {
          if (cm.getAction().equals("adds")) {
            if (cm.getAdds().getClass_().getName().equals(cl.getName())) {
              if (cm.getAdds().getClass_().getExtends() != null) parentClasses.add(cm.getAdds().getClass_().getExtends());
              for (Method method : cm.getAdds().getClass_().getMethod())
                if (method.getReference().getName().equals(name))
                  return method.getReturntype(); 
            }
          } else {
            if ((cm.getAction().equals("modifies")) &&
              (cm.getModifies().getClass_().getName().equals(cl.getName())))
            if (cm.getModifies().getExtends() != null) parentClasses.add(cm.getModifies().getExtends());
            for (AddsMethod amethod : cm.getModifies().getMethod().getAddsList())
              if (amethod.getMethod().getReference().getName().equals(name))
                return amethod.getMethod().getReturntype();
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
    module = new ContainingModuleFinded().lookup(cl);
    p = new ContainingProgramFinded().lookup(module);
    Collection<Import> importList = p.getImports();
    moduleList.addAll(p.getModulesList());
    Program current;
    for (Import imp : importList) {
      Resource resource = EcoreUtil2.getResource(p.eResource(), imp.getImportURI());
      current = (Program)resource.getContents().get(0);
      moduleList.addAll(current.getModulesList());
    }
    for (Module mod : moduleList) {
      if (mod.getNtype() != null)
      if (mod.getNtype().equals("core")){
        for (Class c : mod.getCore().getClassesList())
          if (c.getName().equals(cl.getName())) {
            if (c.getExtends() != null) parentClasses.add(c.getExtends());
            for (Field f : c.getField())
              if (f.getReference().getName().equals(name))
                return f.getType();
          }
      }else {
        for (Classm cm : mod.getDelta().getClassesList()) {
          if (cm.getAction().equals("adds")) {
            if (cm.getAdds().getClass_().getName().equals(cl.getName())) {
              if (cm.getAdds().getClass_().getExtends() != null) parentClasses.add(cm.getAdds().getClass_().getExtends());
              for (Field f : cm.getAdds().getClass_().getField())
                if (f.getReference().getName().equals(name))
                  return f.getType(); 
            }
          } else {
            if ((cm.getAction().equals("modifies")) &&
              (cm.getModifies().getClass_().getName().equals(cl.getName())))
            if (cm.getModifies().getExtends() != null) parentClasses.add(cm.getModifies().getExtends());
            for (AddsField af : cm.getModifies().getField().getAddsList())
              if (af.getField().getReference().getName().equals(name))
                return af.getField().getType();
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

  public ClassType getTypeExpression(Expression expression, Map <String, CST> classMapApply){
	  Class temp1 = null;
	  ClassType t1 = null;
	  String tipo = "";
	  TerminalExpression te = expression.getTerminalExpression();
	  if (te == null) {
          t1 = checkType(expression);
        }
        else if (te.getCast() != null) {
          if (te.getCast().getExpression() != null) {
            temp1 = te.getCast().getType();
          }
        } else if (te.getNew() != null) {
          temp1 = te.getNew().getType();
        } else if (te.getThis() != null) {
          temp1 = new ContainingClassFinded().lookup(expression.getTerminalExpression());
          if(temp1 == null){
        	  Classm temp1m = new ContainingClassmFinded().lookup(expression.getTerminalExpression());
        	  if(temp1m.getAction().equals("adds"))
        		  temp1 = temp1m.getAdds().getClass_();
        	  else
        		  temp1 = temp1m.getModifies().getClass_();
          }
        } else if (te.getVariable() != null) {
          if (te.getVariable().getParameter() != null) {
            t1.setType(te.getVariable().getParameter().getType());
          } else {
            String name = te.getVariable().getFieldRef().getName();
            Class tempClass1 = new ContainingClassFinded().lookup(te);
            if (tempClass1 == null) {
              Classm cm = new ContainingClassmFinded().lookup(te);
              if (cm.getAction().equals("adds"))
                tempClass1 = cm.getAdds().getClass_();
              else
                tempClass1 = cm.getModifies().getClass_();
            }
            t1.setType(new AuxiliaryFunctions().checkTypeField(name, tempClass1));
          }
        } else if (te.getOriginal() != null) {
          ModifiesMethod originalMethod = new ContainingModifiesMethodFinded().lookup(te.getOriginal());
          if (originalMethod != null)
            t1.setType(originalMethod.getReturntype());
          else {
            //error("Cannot use this expression", expression, Integer.valueOf(31));
          }
        }
        else if(te.getString() != null) {
        	  temp1 = classMapApply.get("String").getClasse();
          }
        else if(te.getInt() != null) {
        	  tipo = "int";
          }
        else if(te.getNull() != null) {
        	  tipo = "null";
          }
	  ClassType ct = new ClassType();
	  if(t1 != null) 
		  ct = (t1);
	  else if(temp1 != null)
		  ct.setClass(temp1); 
	  else
		  ct.setBasic(tipo);
	  return ct;
	  
  }
  */
  private BigInteger deltaLevel(Delta d, Collection<Delta> deltaDelete) {
    BigInteger level = BigInteger.ZERO;
    for (Delta delta : d.getAfter()) {
      BigInteger levelAfter = deltaLevel(delta, deltaDelete);
      if (level.compareTo(levelAfter) <= 0) {
        level = levelAfter.add(BigInteger.ONE);
      }
    }
    if (level.compareTo(BigInteger.ZERO) == 0)
      level = BigInteger.ONE;
    if (deltaDelete.contains(d))
        return level.subtract(BigInteger.ONE);
    return level;
  }
  public boolean validDeltaWhen(Condition condition, Config config){
	  boolean result = true;
	  if(condition.getFeature() != null){
		  result = config.getFeature().contains(condition.getFeature());
	  }
	  else if(condition.getCondition1() != null){
		  boolean temp1 = validDeltaWhen(condition.getCondition1(), config);
		  boolean temp2 = validDeltaWhen(condition.getCondition2(), config);
		  if (condition.getOperation().equals("||"))
			  result = (temp1) || (temp2);
		  else if (condition.getOperation().equals("&&"))
			  result = (temp1) && (temp2);
		  else if (condition.getOperation().equals("->"))
			  result = (!temp1) || (temp2);
		  else if (condition.getOperation().equals("<->")) 
			  result = temp1 == temp2;
	  }
	  if(condition.getComplement() != null) result = !result;
	  return result;
  }
  public boolean validCondition(Condition condition, Collection<Feature> featureList)
  {
    Collection<String> fn = new LinkedList<String>();
    boolean conditionBoolean = false;
    boolean temp2 = false;
    if (condition.getCondition1() != null) {
      boolean temp1 = validCondition(condition.getCondition1(), featureList);
      temp2 = validCondition(condition.getCondition1(), featureList);
      if (condition.getOperation().equals("||"))
        conditionBoolean = (temp1) || (temp2);
      else if (condition.getOperation().equals("&&"))
        conditionBoolean = (temp1) && (temp2);
      else if (condition.getOperation().equals("->"))
        conditionBoolean = (!temp1) || (temp2);
      else if (condition.getOperation().equals("<->")) {
        conditionBoolean = temp1 == temp2;
      }
    }
    else if (condition.getFeature() != null) {
      for (Feature f : featureList)
        fn.add(f.getName());
      conditionBoolean = fn.contains(condition.getFeature().getName());
    }
    if (condition.getComplement() != null)
      conditionBoolean = !conditionBoolean;
    return conditionBoolean;
  }
  
  public String configurationToString(Program p, Config config){
	  String name ="";
		for(Feature f : config.getFeature())
			name += f.getName() +", ";
		name = name.substring(0, name.length() -2 );
		return name;
  }
  
  /**
   * Returns the list of the constructor that can be invoked within the given body.
   * @param body the target body.
   * 
   * @return the constructor list where if a class 'c' has no constructor a default constructor
   * 'constr' such that constr.getName() = c is appended to the list.<br/>
   * This method returns an empty list if some error occurs (the parameter c is null,
   * the eContainer is null, etc.).
   */
  public Collection<Constructor> getAllAvailableConstructors(MethodBody body) {
		 // throw new UnsupportedOperationException("Operation not still available");
		  Collection<Constructor> allConstructorCall = new HashSet<Constructor>();
		  Module m = new ContainingModuleFinded().lookup(body);
		  Map<BigInteger, Set<Delta>> deltaMap;
		  if(m.getNtype().equals("core"))
			  allConstructorCall.addAll(getAllAvailableConstructorsClasses(m.getCore().getClassesList()));
		  else if(m.getNtype().equals("delta")){
			  allConstructorCall.addAll(getAllAvailableConstructorsClasses(coreClasses(m)));
			  deltaMap = allDeltaLevel((Program)m.eContainer());
			  for(BigInteger b : deltaMap.keySet()){
				  for(Delta d : deltaMap.get(b)){
					  allConstructorCall.addAll(getAllAvailableConstructorsDelta(d));
				  }
				  if(deltaMap.get(b).contains(m.getDelta())) break;
			  }
		  }
		  Program p2 = (Program)DjResourceFactory.getSystemResource().getContents().get(0);
		  Collection<Class> classes = p2.getModulesList().get(0).getCore().getClassesList();
		  allConstructorCall.addAll(getAllAvailableConstructorsClasses(classes));
		  
		  return allConstructorCall;
	  }
	  
	  private Collection<Constructor> getAllAvailableConstructorsClasses(Collection<Class> classes){
		  Collection<Constructor> allConstructorCall = new HashSet<Constructor>();
		  for(Class c : classes){
			  if(c.getName().equals("AllObject"));
			  else if(c.getConstructor().size() != 0)
				  allConstructorCall.addAll(c.getConstructor()); 
			  else{
				  Constructor constructor = DJFactory.eINSTANCE.createConstructor();
			  	  constructor.setName(c);
			  	  allConstructorCall.add(constructor);
			  }
		  }
		  
		  return allConstructorCall;
	  }
	  
	  private Collection<Constructor> getAllAvailableConstructorsDelta(Delta delta){
		  Collection<Constructor> allConstructorCall = new HashSet<Constructor>();
		  for(Classm cm : delta.getClassesList()){
			  if(cm.getAction().equals("adds")){
				  Class c = cm.getAdds().getClass_();
				  if(c.getConstructor().size() != 0)
					  allConstructorCall.addAll(c.getConstructor()); 
				  else{
					  Constructor constructor = DJFactory.eINSTANCE.createConstructor();
					  constructor.setName(c);
					  allConstructorCall.add(constructor);
				  }
			  }
			  else if(cm.getAction().equals("modifies")){
				  if(cm.getModifies().getConstructor() != null)
					  allConstructorCall.add(cm.getModifies().getConstructor());
			  }
		  }
		  
		  return allConstructorCall;
	  }
}