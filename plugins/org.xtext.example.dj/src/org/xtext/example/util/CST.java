package org.xtext.example.util;

import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import org.xtext.example.dJ.Class;
import org.xtext.example.dJ.Constructor;
import org.xtext.example.dJ.Expression;
import org.xtext.example.dJ.Field;
import org.xtext.example.dJ.Method;
import org.xtext.example.dJ.ModifiesMethod;

public class CST
{
  private Class c;
  private Map<String, Method> methodsMap = new HashMap<String, Method>();
  private Map<String, ModifiesMethod> modifiedMethodsMap = new HashMap<String, ModifiesMethod>();
  private Map<String, LinkedList<OriginalModifiesMethod>> originalModifiedMethodsMap = new HashMap<String, LinkedList<OriginalModifiesMethod>>();
  private Map<String, Field> fieldsMap = new HashMap<String, Field>();
  private List<Constructor> constructor = new LinkedList<Constructor>();
  private String extending = new String();

  //FIX ME XTEXT null-checks added
  public CST(Class c) {
	  this.c = c;
    for (Method m : c.getMethod())
      if(m != null && m.getReference() != null) methodsMap.put(m.getReference().getName(), m);
    for (Field f : c.getField())
      if(f != null && f.getReference() != null) fieldsMap.put(f.getReference().getName(), f);
    
    if (c.getConstructor() != null)
      if(c != null && c.getConstructor() != null) constructor.addAll(c.getConstructor());
    if (c.getExtends() != null)
      if(c != null && c.getExtends() != null) extending = c.getExtends().getName();
  }

  public boolean addMethod(Method method)
  {
    if (containsMethod(method.getReference().getName()))
      return false;
    methodsMap.put(method.getReference().getName(), method);
    return true;
  }
  public boolean addModifiesMethod(ModifiesMethod method) {
    if (!containsMethod(method.getMethodRef().getName()))
      return false;
    boolean originalCall = false;
    if (method.getBody() != null) {
        Collection<Expression> expressions = method.getBody().getExpressions();
        if (method.getBody().getExpressionReturn() != null) {
        	if (end(method.getBody().getExpressionReturn(), method)){
        		for (Expression ex : expressions)
        			if (!end(ex, method)){
        				originalCall = true;
        				break;
        			}
        	}else originalCall = true; 
        }
        else
        	for (Expression ex : expressions)
        		if (!end(ex, method)){
        			originalCall = true;
        			break;
        		}
    }
    if(!originalCall) 
    	originalModifiedMethodsMap.remove(method.getMethodRef().getName());
    modifiedMethodsMap.put(method.getMethodRef().getName(), method);
    return true;
  }

  public boolean addField(Field field) {
    if (containsField(field.getReference().getName()))
      return false;
    fieldsMap.put(field.getReference().getName(), field);
    return true;
  }
  public void setExtending(Class c) {
	this.extending = c.getName();
  }
  public void setExtending(String name) {
	this.extending = name;
  }
  public String getExtending() {
    return extending;
  }
  public void setConstructor(Constructor c) {
	this.constructor.clear();
    this.constructor.add(c);
  }
  public List<Constructor> getConstructor() {
    return constructor;
  }	  
  public boolean removeMethod(String method) {
    if (!containsMethod(method))
      return false;
    methodsMap.remove(method);
    removeModifiesMethod(method);
    return true;
  }
  public boolean removeModifiesMethod(String method) {
    if (!containsMethod(method))
      return false;
    modifiedMethodsMap.remove(method);
    return true;
  }
  public boolean removeField(String field) {
    if (!containsField(field))
      return false;
    fieldsMap.remove(field);
    return true;
  }
  public boolean containsMethod(String method) {
    return methodsMap.containsKey(method);
  }
  public boolean containsModifiesMethod(String method) {
    return modifiedMethodsMap.containsKey(method);
  }
  public boolean containsField(String field) {
    return fieldsMap.containsKey(field);
  }
  public Collection<Method> getMethodList() {
    Collection<Method> m = new LinkedList<Method>();
    for (Method method : methodsMap.values()) {
      if (!containsModifiesMethod(method.getReference().getName())) {
        m.add(method);
      } else {
        Collection<OriginalModifiesMethod> mod = originalModifiedMethodsMap.get(method.getReference().getName());
        if (mod != null)
          for (OriginalModifiesMethod original : mod)
            if (original.getMethod() != null)
              m.add(original.getMethod());
      }
    }
    return m;
  }
  public Collection<Field> getFieldList() {
    return fieldsMap.values();
  }
  public Collection<ModifiesMethod> getModifiesMethodList() {
    LinkedList<ModifiesMethod> m = new LinkedList<ModifiesMethod>();
    //m.addAll(modifiedMethodsMap.values());
    for (ModifiesMethod method : modifiedMethodsMap.values()) {
      Collection<OriginalModifiesMethod> mod = originalModifiedMethodsMap.get(method.getMethodRef().getName());
      m.addLast(method);
      if (mod != null)
        for (OriginalModifiesMethod original : mod)
          if (original.getMethodm() != null)
            m.addLast(original.getMethodm());
    }
    return m;
  }
  
  public Class getClasse(){
	  return c;
  }

  public boolean isOriginalMethod(Method m){
	  for(OriginalModifiesMethod original : originalModifiedMethodsMap.get(m.getReference().getName()))
			  if(original.getMethod().equals(m))
				  return true;
	  return false;
  }
  public boolean isOriginalModifiesMethod(ModifiesMethod m){
	  for(OriginalModifiesMethod original : originalModifiedMethodsMap.get(m.getMethodRef().getName()))
			  if(original.getMethodm().equals(m))
				  return true;
	  return false;
  }
  private boolean end(Expression ex, ModifiesMethod method) {
    boolean end = true;
    while ((ex != null) && (end))
      if ((ex.getTerminalExpression() != null) && (ex.getTerminalExpression().getOriginal() != null)) {
        end = false;
        if (originalModifiedMethodsMap.containsKey(method.getMethodRef().getName()))
        {
          OriginalModifiesMethod original;
          if ((!modifiedMethodsMap.containsKey(method.getMethodRef().getName())) && (methodsMap.containsKey(method.getMethodRef().getName()))) {
            original = new OriginalModifiesMethod(methodsMap.get(method.getMethodRef().getName()));
          }
          else {
            original = new OriginalModifiesMethod(modifiedMethodsMap.get(method.getMethodRef().getName()));
          }
          (originalModifiedMethodsMap.get(method.getMethodRef().getName())).addFirst(original);
        }
        else
        {
          LinkedList<OriginalModifiesMethod> set = new LinkedList<OriginalModifiesMethod>();
          OriginalModifiesMethod original;
          if ((!modifiedMethodsMap.containsKey(method.getMethodRef().getName())) && (methodsMap.containsKey(method.getMethodRef().getName()))) {
            original = new OriginalModifiesMethod(methodsMap.get(method.getMethodRef().getName()));
          }
          else {
            original = new OriginalModifiesMethod(modifiedMethodsMap.get(method.getMethodRef().getName()));
          }
          set.add(original);
          originalModifiedMethodsMap.put(method.getMethodRef().getName(), set);
        }
      }
      else {
        ex = ex.getReceiver();
      }
    return end;
  }

  private class OriginalModifiesMethod
  {
    private Method method;
    private ModifiesMethod methodm;

    OriginalModifiesMethod(Method method)
    {
      this.methodm = null;
      this.method = method;
    }
    OriginalModifiesMethod(ModifiesMethod methodm) {
      this.method = null;
      this.methodm = methodm;
    }
    public Method getMethod() {
      return this.method;
    }
    public ModifiesMethod getMethodm() {
      return this.methodm;
    }
  }
}