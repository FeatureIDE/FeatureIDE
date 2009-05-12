package featureide.ui.collaborationdiagram;

import java.util.ArrayList;

/**
 * represents a class; split in roles
 * 
 * @author yesnice
 *
 */
public class CD_Class {
	
	private String name;
	private ArrayList<CD_Role> roles;

	public CD_Class() {
		name = new String();
		roles = new ArrayList<CD_Role>();
	}
	
	public CD_Class(String name, ArrayList<CD_Role> roles) {
		this.name = name;
		this.roles = roles;
	}
	
	public void addRole(CD_Role role) {
		this.getRoles().add(role);
	}

	public void setRoles(ArrayList<CD_Role> roles) {
		this.roles = roles;
	}

	public ArrayList<CD_Role> getRoles() {
		return roles;
	}

	public void setName(String name) {
		this.name = name;
	}

	public String getName() {
		return name;
	}

}
