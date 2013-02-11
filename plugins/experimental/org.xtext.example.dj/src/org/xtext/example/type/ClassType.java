package org.xtext.example.type;

import java.util.Map;

import org.xtext.example.lookup.AuxiliaryFunctions;
import org.xtext.example.dJ.Type;
import org.xtext.example.dJ.Class;
import org.xtext.example.util.CST;

public class ClassType {
	@SuppressWarnings("unused")
	private final String OBJECT = "Object";
	private final String NULL = "null";
	private String basic;
	private Class c;
	public String getBasicType(){
		return basic;
	}
	public Class getClassType(){
		return c;
	}
	public void setType(Type type){
		if(type != null){
			this.basic = type.getBasic();
			this.c = type.getClassref();
		}
	}
	public void setClass(Class c){
		this.c = c;
	}
	public void setBasic(String basic){
		this.basic = basic;
	}
	
	/*
	 * Chiama il metodo equals sottostante.
	 */
	public boolean equals(Type type, Map<String, CST> classMapApply){
		ClassType ct = new ClassType();
		ct.setType(type);
		return equals(ct, classMapApply);
	}
	
	
	/*
	 * Ritorna true se la classe passata come parametro � una parent class o la medesima classe 
	 * di quella su cui il metodo � stato chiamato.
	 * O ancora se hanno lo stesso basic type.
	 * AllObject � stato usato per scopi specifici riguardati la SystemOutWrapped
	 */
	public boolean equals(ClassType type, Map<String, CST> classMapApply){
		if(type != null)
			if(type.getClassType() != null && "AllObject".equals(type.getClassType().getName())) return true;
			else if(type.getBasicType() != null)
				return(type.getBasicType().equals(basic));
			else if(c != null && type.getClassType() != null)
				return(new AuxiliaryFunctions().isParentClass(c.getName(), type.getClassType().getName(), classMapApply ));
			else if(type.getClassType() != null)
	               return(NULL.equals(basic));
		return false;
	}
}
