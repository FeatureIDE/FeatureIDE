package org.xtext.example.util;

import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Map;
import java.util.Set;
import org.xtext.example.dJ.Class;
import org.xtext.example.dJ.*;

public class ACST
{
  private Map<String, Method> methodsMap = new HashMap<String, Method>();
  private Map<String, Field> fieldsMap = new HashMap<String, Field>();
  private Set<Constructor> constructorsSet = new HashSet<Constructor>();
  private Set<String> extendingSet = new HashSet<String>();

  public ACST(Class c) {
    for (Method m : c.getMethod())
      methodsMap.put(m.getReference().getName(), m);
    for (Field f : c.getField())
      fieldsMap.put(f.getReference().getName(), f);
    if (c.getConstructor() != null)
      constructorsSet.addAll(c.getConstructor());
    if (c.getExtends() != null)
      extendingSet.add(c.getExtends().getName()); 
  }

  public boolean setMethods(Method method) {
    if (!methodsMap.containsKey(method.getReference().getName())) {
      methodsMap.put(method.getReference().getName(), method);
      return true;
    }

    Method m = (Method)this.methodsMap.get(method.getReference().getName());
    LinkedList<String> paramList1 = new LinkedList<String>();
    LinkedList<String> paramList2 = new LinkedList<String>();
    if (m.getReturntype().getBasic() == null)
      if (method.getReturntype().getBasic() == null){
        if (!m.getReturntype().getClassref().getName().equals(method.getReturntype().getClassref().getName()))
          return false;
      }else
        return false;
    if (m.getReturntype().getBasic().equals(method.getReturntype().getBasic())) {
      for (Parameter p : m.getParams())
        if (p.getType().getBasic() == null)
          paramList1.add(p.getType().getClassref().getName());
        else
          paramList1.add(p.getType().getBasic());
      for (Parameter p : method.getParams())
        if (p.getType().getBasic() == null)
          paramList2.add(p.getType().getClassref().getName());
        else
          paramList2.add(p.getType().getBasic());
      return paramList1.equals(paramList2);
    }

    return false;
  }

  public boolean setFields(Field field) {
    if (!fieldsMap.containsKey(field.getReference().getName())) {
      fieldsMap.put(field.getReference().getName(), field);
      return true;
    }

    Field f = fieldsMap.get(field.getReference().getName());
    if (f.getType().getBasic() == null) {
      if (field.getType().getBasic() == null)
        return f.getType().getClassref().getName().equals(field.getType().getClassref().getName());
      return false;
    }return f.getType().getBasic().equals(field.getType().getBasic());
  }

  public boolean setConstructors(Constructor constructor) {
    return !constructorsSet.add(constructor);
  }
  public boolean setExtending(Class extending) {
    return !extendingSet.add(extending.getName());
  }
  public boolean modifiesMethod(ModifiesMethod method1, String methodName2) {
    if ((this.methodsMap.get(method1.getMethodRef().getName()) != null) && 
      (this.methodsMap.get(methodName2) != null)) {
      Method method2 = (Method)this.methodsMap.get(methodName2);
      LinkedList<String> paramList1 = new LinkedList<String>();
      LinkedList<String> paramList2 = new LinkedList<String>();
      if (method1.getReturntype().getBasic() == null)
        if (method2.getReturntype().getBasic() == null){
          if (!method1.getReturntype().getClassref().getName().equals(method2.getReturntype().getClassref().getName()))
            return false;
    	}
        else
            return false;
      else if (!method1.getReturntype().getBasic().equals(method2.getReturntype().getBasic()))
        return false;
      for (Parameter p : method1.getParams())
        if (p.getType().getBasic() == null)
          paramList1.add(p.getType().getClassref().getName());
        else
          paramList1.add(p.getType().getBasic());
      for (Parameter p : method2.getParams())
        if (p.getType().getBasic() == null)
          paramList2.add(p.getType().getClassref().getName());
        else
          paramList2.add(p.getType().getBasic());
      if (!paramList1.equals(paramList2)) {
          return false;
        }
    }
    return true;
  }
 

  public Set<String> getExtending() {
    return extendingSet;
  }
  public Set<Constructor> getConstructor() {
    return constructorsSet;
  }
  public Map<String, Method> getMethods() {
    return methodsMap;
  }
  public Map<String, Field> getFields() {
    return fieldsMap;
  }
}