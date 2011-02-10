package org.xtext.example.linking;
import java.lang.reflect.Modifier;
import java.util.Collection;
import java.util.HashMap;
import java.util.Map;

import org.eclipse.emf.common.util.EList;
import org.xtext.example.dJ.Class;
import org.xtext.example.dJ.Constructor;
import org.xtext.example.dJ.DJFactory;
import org.xtext.example.dJ.Method;
import org.xtext.example.dJ.MethodRef;
import org.xtext.example.dJ.Parameter;
import org.xtext.example.dJ.Type;

public class ElementFactory {
	private Map<String, Class> classes;
	
	private Map<String, String> djJavaNames;
	
	private static final ElementFactory instance = new ElementFactory();
	
	/**
	 * Creates a new element factory.
	 */
	protected ElementFactory() {
		//Init tables
		initClasses();
		//Forall element --> create
		try {
			djJavaNames = new HashMap<String, String>();
			createAllObject("AllObject", "AllObject");
			createClass("Object", "java.lang.Object");
			createClass("Thread", "java.lang.Thread");
			createClass("String", "java.lang.String");
			createClass("Byte", "java.lang.Byte");
			createClass("Short", "java.lang.Short");
			createClass("Integer", "java.lang.Integer");
			createClass("Long", "java.lang.Long");
			createClass("Float", "java.lang.Float");
			createClass("Double", "java.lang.Double");
			createClass("BigInteger", "java.math.BigInteger");
			createClass("BigDecimal", "java.math.BigDecimal");
			createClass("LinkedList", "java.util.LinkedList");
			createClass("Thread", "java.lang.Thread");
			createPrintStream("SystemOutWrapper", "SystemOutWrapper");
			createMyMath("MyMath", "MyMath");
			createClass("Lock", "java.util.concurrent.locks.ReentrantLock");
		} catch(ClassNotFoundException ex) {
			throw new RuntimeException(ex);
		}
	}
	
	public Class forName(String name) {
		return classes.get(name);
	}
	
	/**
	 * Convert the given dj element name into
	 * the corresponding java element name.
	 * for instance, toJavaName("IObject") = "Object"
	 * @param name the dj element name to convert
	 * @return the dj java name mapping or <code>null</code> if
	 * the name is not mapping a java class.
	 */
	public String toSimpleJavaName(String name) {
		return djJavaNames.get(name);
	}
	
	/**
	 * Convert the given swrtj element name into
	 * the corresponding java element name.
	 * for instance, toJavaName("IObject") = "Object"
	 * @param name the swrtj element name to convert
	 * @return the swrtj java name mapping with optionally generic parameters
	 * as Object, or <code>null</code> if
	 * the name is not mapping a java class.
	 */
	public String toJavaName(String name) {
		String javaName = toSimpleJavaName(name);
		
		try{
			if(javaName != null && java.lang.Class.forName(javaName).getTypeParameters().length == 1) {
				javaName += "<java.lang.Object>";
			}
		} catch(ClassNotFoundException ex) {
			throw new RuntimeException(ex);
		}
		
		return javaName;
	}
	
	/**
	 * Returns all the elements mapped from java to swrtj.
	 * @return the element mapping sdjName --> element.
	 */
	public Map<String, Class> getElements() {
		Map<String, Class> result = new HashMap<String, Class>();
		Collection<Class> classList = classes.values();
		
		for(Class c : classList){
			result.put(c.getName(), c);
		}
		
		return result;
	}
	
	/**
	 * Returns all the elements mapped from java to dj.
	 * @return the element list
	 */
	public Collection<Class> getElementList() {
		return getElements().values();
	}
	
	/**
	 * Returns the singleton factory instance.
	 * @return the factory instance.
	 */
	public static ElementFactory getFactory() {
		return instance;
	}
	
	/*Service methods*/
	
	@SuppressWarnings("unused")
	private void createClass(String djName, String javaName) throws ClassNotFoundException {
		map(djName, javaName);
		Class result = classes.get(djName);
		java.lang.Class<?> c = java.lang.Class.forName(javaName);
		result.setName(djName);
		java.lang.reflect.Constructor<?>[] constructors = c.getConstructors();
		for(java.lang.reflect.Constructor<?> cons : constructors){
			Constructor constructor = constructorConvert(djName, cons, result);
			if(constructor != null) result.getConstructor().add(constructor);
		}
		java.lang.reflect.Method[] methods = c.getMethods();
		java.lang.reflect.Field[] fields = c.getFields();
		
		for(java.lang.reflect.Method m : methods) {
			Method method = methodConvert(m);
			if(method != null) result.getMethod().add(method);
		}
	/*	for(java.lang.reflect.Field f : fields){
			Field field = fieldConvert(f);
			
			if(field != null){
				result.getField().add(field);
			}
		}*/
	}
	
	private Constructor constructorConvert(String name, java.lang.reflect.Constructor<?> constructor, Class owner) {
		Constructor result = DJFactory.eINSTANCE.createConstructor();
		result.setName(owner);
		java.lang.Class<?>[] javaParameters = constructor.getParameterTypes();
		int counter = 1;
				
		for(java.lang.Class<?> javaType : javaParameters) {
			Parameter parameter = DJFactory.eINSTANCE.createParameter();
			Type parameterType = typeConvert(javaType);
			if(parameterType == null) return null;
			
			parameter.setName("par" + counter);
			parameter.setType(parameterType);
			result.getParams().add(parameter);
			counter++;
		}
		
		return result;
	}
	
	private Method methodConvert(java.lang.reflect.Method method) {
		if(Modifier.isStatic(method.getModifiers())) return null;
		
		Method result = DJFactory.eINSTANCE.createMethod();
	
		Type returnType = typeConvert(method.getReturnType());
		if(returnType == null) return null;
		result.setReturntype(returnType);
		
		MethodRef methodRef = DJFactory.eINSTANCE.createMethodRef();
		methodRef.setName(method.getName());
		result.setReference(methodRef);
		
		java.lang.Class<?>[] javaParameters = method.getParameterTypes();
		int counter = 1;
				
		for(java.lang.Class<?> javaType : javaParameters) {
			Parameter parameter = DJFactory.eINSTANCE.createParameter();
			Type parameterType = typeConvert(javaType);
			if(parameterType == null) return null;
			
			parameter.setName("par" + counter);
			parameter.setType(parameterType);
			result.getParams().add(parameter);
			counter++;
		}
		
		return result;
	}
	/*private Field fieldConvert(java.lang.reflect.Field field) {
		if(Modifier.isPrivate(field.getModifiers())) return null;
		Field result = DJFactory.eINSTANCE.createField();
		Type type = typeConvert(field.getType());
		if(type == null) return null;
		result.setType(type);
		
		FieldRef fieldRef = DJFactory.eINSTANCE.createFieldRef();
		fieldRef.setName(field.getName());
		result.setReference(fieldRef);

		return result;
	}
*/
	private Type typeConvert(java.lang.Class<?> type) {  
		String name = type.getName();
		Type result = DJFactory.eINSTANCE.createType();
		
		if(name.equals("short") || name.equals("int") || name.equals("long") ||
		   name.equals("float") || name.equals("double") || name.equals("char") ||
		   name.equals("boolean") || name.equals("void")) {
			result.setBasic(name);
		} else if(name.equals("java.lang.Object")) {
			result.setClassref(classes.get("Object"));
		} else if(name.equals("java.lang.String")) {
			result.setClassref(classes.get("String"));
		} else if(name.equals("java.lang.Byte")) {
			result.setClassref(classes.get("Byte"));
		} else if(name.equals("java.lang.Short")) {
			result.setClassref(classes.get("Short"));
		} else if(name.equals("java.lang.Integer")) {
			result.setClassref(classes.get("Integer"));
		} else if(name.equals("java.lang.Long")) {
			result.setClassref(classes.get("Long"));
		} else if(name.equals("java.lang.Float")) {
			result.setClassref(classes.get("Float"));
		} else if(name.equals("java.lang.Double")) {
			result.setClassref(classes.get("Double"));
		} else if(name.equals("java.math.BigInteger")) {
			result.setClassref(classes.get("BigInteger"));
		} else if(name.equals("java.math.BigDecimal")) {
			result.setClassref(classes.get("BigDecimal"));
		} else if(name.equals("java.util.LinkedList")) {
			result.setClassref(classes.get("LinkedList"));
		} else if(name.equals("java.util.Scanner")) {
			result.setClassref(classes.get("Scanner"));
		} else if(name.equals("java.lang.Thread")) {
			result.setClassref(classes.get("Thread"));
		} else if(name.equals("SystemOutWrapper")) {
			result.setClassref(classes.get("SystemOutWrapper"));
		} else if(name.equals("MyMath")) {
			result.setClassref(classes.get("MyMath"));
		} else if(name.equals("java.lang.Runnable")) {
			result.setClassref(classes.get("Runnable"));
		} else if(name.equals("java.util.concurrent.locks.Lock")) {
			result.setClassref(classes.get("Lock"));
		} else { 
			result = null;
		}
		return result;
	}

	
	private void initClasses() {
		classes = new HashMap<String, Class>();
		
		classes.put("AllObject", DJFactory.eINSTANCE.createClass());
		classes.put("Object", DJFactory.eINSTANCE.createClass());
		classes.put("Byte", DJFactory.eINSTANCE.createClass());
		classes.put("Short", DJFactory.eINSTANCE.createClass());
		classes.put("Integer", DJFactory.eINSTANCE.createClass());
		classes.put("Long", DJFactory.eINSTANCE.createClass());
		classes.put("Float", DJFactory.eINSTANCE.createClass());
		classes.put("Double", DJFactory.eINSTANCE.createClass());
		classes.put("String", DJFactory.eINSTANCE.createClass());
		classes.put("BigInteger", DJFactory.eINSTANCE.createClass());
		classes.put("BigDecimal", DJFactory.eINSTANCE.createClass());
		classes.put("LinkedList", DJFactory.eINSTANCE.createClass());
		classes.put("SystemOutWrapper", DJFactory.eINSTANCE.createClass());
		classes.put("Thread", DJFactory.eINSTANCE.createClass());
		classes.put("Lock", DJFactory.eINSTANCE.createClass());
		classes.put("MyMath", DJFactory.eINSTANCE.createClass());
	}
	
	private void map(String djName, String javaName) {
		djJavaNames.put(djName, javaName);
	}
	
	private void createAllObject(String djName, String javaName) throws ClassNotFoundException {
		map(djName, javaName);
		Class result = classes.get(djName);
		result.setName(djName);
	}
	private void createPrintStream(String djName, String javaName) throws ClassNotFoundException {
		map(djName, javaName);
		Class result = classes.get(djName);
		result.setName(djName);
		
		Constructor construct = DJFactory.eINSTANCE.createConstructor();
		construct.setName(result);
		result.getConstructor().add(construct);
		
		EList<Method> methodList = result.getMethod();
		Method method = DJFactory.eINSTANCE.createMethod();
		Parameter parameter = DJFactory.eINSTANCE.createParameter();
		Type type = DJFactory.eINSTANCE.createType();
		Type returnType = DJFactory.eINSTANCE.createType();
		MethodRef methodRef = DJFactory.eINSTANCE.createMethodRef();
		methodRef.setName("print");
		method.setReference(methodRef);
		parameter.setName("output");
		type.setClassref(forName("AllObject"));
		returnType.setBasic("void");
		parameter.setType(type);
		method.getParams().add(parameter);
		method.setReturntype(returnType);
		methodList.add(method);
		
		method = DJFactory.eINSTANCE.createMethod();
		parameter = DJFactory.eINSTANCE.createParameter();
		type = DJFactory.eINSTANCE.createType();
		returnType = DJFactory.eINSTANCE.createType();
		methodRef = DJFactory.eINSTANCE.createMethodRef();
		methodRef.setName("println");
		method.setReference(methodRef);
		parameter.setName("output");
		type.setClassref(forName("AllObject"));
		returnType.setBasic("void");
		parameter.setType(type);
		method.getParams().add(parameter);
		method.setReturntype(returnType);
		methodList.add(method);
		
	}	
	
	
	private void createMyMath(String djName, String javaName) throws ClassNotFoundException {
		map(djName, javaName);
		Class result = classes.get(djName);
		result.setName(djName);
		
		Constructor construct = DJFactory.eINSTANCE.createConstructor();
		construct.setName(result);
		result.getConstructor().add(construct);
		
		EList<Method> methodList = result.getMethod();
		Method method = DJFactory.eINSTANCE.createMethod();
		Parameter parameter = DJFactory.eINSTANCE.createParameter();
		Parameter parameter2 = DJFactory.eINSTANCE.createParameter();
		Type type = DJFactory.eINSTANCE.createType();
		Type type2 = DJFactory.eINSTANCE.createType();
		Type returnType = DJFactory.eINSTANCE.createType();
		MethodRef methodRef = DJFactory.eINSTANCE.createMethodRef();
		methodRef.setName("add");
		method.setReference(methodRef);
		parameter.setName("a");
		type.setBasic("int");
		parameter.setType(type);
		method.getParams().add(parameter);
		parameter2.setName("b");
		type2.setBasic("int");
		parameter2.setType(type2);
		method.getParams().add(parameter2);
		returnType.setBasic("int");
		method.setReturntype(returnType);
		methodList.add(method);
		
		method = DJFactory.eINSTANCE.createMethod();
		parameter = DJFactory.eINSTANCE.createParameter();
		parameter2 = DJFactory.eINSTANCE.createParameter();
		type = DJFactory.eINSTANCE.createType();
		type2 = DJFactory.eINSTANCE.createType();
		returnType = DJFactory.eINSTANCE.createType();
		methodRef = DJFactory.eINSTANCE.createMethodRef();
		methodRef.setName("sub");
		method.setReference(methodRef);
		parameter.setName("a");
		type.setBasic("int");
		parameter.setType(type);
		method.getParams().add(parameter);
		parameter2.setName("b");
		type2.setBasic("int");
		parameter2.setType(type2);
		method.getParams().add(parameter2);
		returnType.setBasic("int");
		method.setReturntype(returnType);
		methodList.add(method);
		
		method = DJFactory.eINSTANCE.createMethod();
		parameter = DJFactory.eINSTANCE.createParameter();
		parameter2 = DJFactory.eINSTANCE.createParameter();
		type = DJFactory.eINSTANCE.createType();
		type2 = DJFactory.eINSTANCE.createType();
		returnType = DJFactory.eINSTANCE.createType();
		methodRef = DJFactory.eINSTANCE.createMethodRef();
		methodRef.setName("multiply");
		method.setReference(methodRef);
		parameter.setName("a");
		type.setBasic("int");
		parameter.setType(type);
		method.getParams().add(parameter);
		parameter2.setName("b");
		type2.setBasic("int");
		parameter2.setType(type2);
		method.getParams().add(parameter2);
		returnType.setBasic("int");
		method.setReturntype(returnType);
		methodList.add(method);
		
		method = DJFactory.eINSTANCE.createMethod();
		parameter = DJFactory.eINSTANCE.createParameter();
		parameter2 = DJFactory.eINSTANCE.createParameter();
		type = DJFactory.eINSTANCE.createType();
		type2 = DJFactory.eINSTANCE.createType();
		returnType = DJFactory.eINSTANCE.createType();
		methodRef = DJFactory.eINSTANCE.createMethodRef();
		methodRef.setName("divide");
		method.setReference(methodRef);
		parameter.setName("a");
		type.setBasic("int");
		parameter.setType(type);
		method.getParams().add(parameter);
		parameter2.setName("b");
		type2.setBasic("int");
		parameter2.setType(type2);
		method.getParams().add(parameter2);
		returnType.setBasic("int");
		method.setReturntype(returnType);
		methodList.add(method);
		
		method = DJFactory.eINSTANCE.createMethod();
		parameter = DJFactory.eINSTANCE.createParameter();
		parameter2 = DJFactory.eINSTANCE.createParameter();
		type = DJFactory.eINSTANCE.createType();
		type2 = DJFactory.eINSTANCE.createType();
		returnType = DJFactory.eINSTANCE.createType();
		methodRef = DJFactory.eINSTANCE.createMethodRef();
		methodRef.setName("max");
		method.setReference(methodRef);
		parameter.setName("a");
		type.setBasic("int");
		parameter.setType(type);
		method.getParams().add(parameter);
		parameter2.setName("b");
		type2.setBasic("int");
		parameter2.setType(type2);
		method.getParams().add(parameter2);
		returnType.setBasic("int");
		method.setReturntype(returnType);
		methodList.add(method);
		
		method = DJFactory.eINSTANCE.createMethod();
		parameter = DJFactory.eINSTANCE.createParameter();
		parameter2 = DJFactory.eINSTANCE.createParameter();
		type = DJFactory.eINSTANCE.createType();
		type2 = DJFactory.eINSTANCE.createType();
		returnType = DJFactory.eINSTANCE.createType();
		methodRef = DJFactory.eINSTANCE.createMethodRef();
		methodRef.setName("min");
		method.setReference(methodRef);
		parameter.setName("a");
		type.setBasic("int");
		parameter.setType(type);
		method.getParams().add(parameter);
		parameter2.setName("b");
		type2.setBasic("int");
		parameter2.setType(type2);
		method.getParams().add(parameter2);
		returnType.setBasic("int");
		method.setReturntype(returnType);
		methodList.add(method);
		
		method = DJFactory.eINSTANCE.createMethod();
		parameter = DJFactory.eINSTANCE.createParameter();
		parameter2 = DJFactory.eINSTANCE.createParameter();
		type = DJFactory.eINSTANCE.createType();
		type2 = DJFactory.eINSTANCE.createType();
		returnType = DJFactory.eINSTANCE.createType();
		methodRef = DJFactory.eINSTANCE.createMethodRef();
		methodRef.setName("equals");
		method.setReference(methodRef);
		parameter.setName("a");
		type.setBasic("int");
		parameter.setType(type);
		method.getParams().add(parameter);
		parameter2.setName("b");
		type2.setBasic("int");
		parameter2.setType(type2);
		method.getParams().add(parameter2);
		returnType.setBasic("boolean");
		method.setReturntype(returnType);
		methodList.add(method);
		
		method = DJFactory.eINSTANCE.createMethod();
		parameter = DJFactory.eINSTANCE.createParameter();
		parameter2 = DJFactory.eINSTANCE.createParameter();
		type = DJFactory.eINSTANCE.createType();
		type2 = DJFactory.eINSTANCE.createType();
		returnType = DJFactory.eINSTANCE.createType();
		methodRef = DJFactory.eINSTANCE.createMethodRef();
		methodRef.setName("compare");
		method.setReference(methodRef);
		parameter.setName("a");
		type.setBasic("int");
		parameter.setType(type);
		method.getParams().add(parameter);
		parameter2.setName("b");
		type2.setBasic("int");
		parameter2.setType(type2);
		method.getParams().add(parameter2);
		returnType.setBasic("int");
		method.setReturntype(returnType);
		methodList.add(method);
		
		method = DJFactory.eINSTANCE.createMethod();
		parameter = DJFactory.eINSTANCE.createParameter();
		type = DJFactory.eINSTANCE.createType();
		returnType = DJFactory.eINSTANCE.createType();
		methodRef = DJFactory.eINSTANCE.createMethodRef();
		methodRef.setName("abs");
		method.setReference(methodRef);
		parameter.setName("a");
		type.setBasic("int");
		parameter.setType(type);
		method.getParams().add(parameter);
		returnType.setBasic("int");
		method.setReturntype(returnType);
		methodList.add(method);
		
		method = DJFactory.eINSTANCE.createMethod();
		parameter = DJFactory.eINSTANCE.createParameter();
		type = DJFactory.eINSTANCE.createType();
		returnType = DJFactory.eINSTANCE.createType();
		methodRef = DJFactory.eINSTANCE.createMethodRef();
		methodRef.setName("not");
		method.setReference(methodRef);
		parameter.setName("a");
		type.setBasic("int");
		parameter.setType(type);
		method.getParams().add(parameter);
		returnType.setBasic("int");
		method.setReturntype(returnType);
		methodList.add(method);
		
	}	
	
}