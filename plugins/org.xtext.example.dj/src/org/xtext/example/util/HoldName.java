package org.xtext.example.util;

public class HoldName {
	String name;
	int cont;
	HoldName(String name, int cont){
		this.name = name;
		this.cont = cont;
	}
	public String getName(){
		return name;
	}
	public int getCont(){
		return cont;
	}
	public void setName(String name){
		this.name = name;
	}
	public void setCont(int cont){
		this.cont = cont;
	}
}
