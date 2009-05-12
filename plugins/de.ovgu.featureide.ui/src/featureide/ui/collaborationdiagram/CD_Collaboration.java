package featureide.ui.collaborationdiagram;

import java.util.ArrayList;

/**
 * contains all roles belonging to one feature
 * @author yesnice
 *
 */
public class CD_Collaboration {
	
	/**
	 * the name of the collaboration, i.e. the name of the feature
	 */
	private String name;
	
	private ArrayList<CD_Role> roles;
	
	public CD_Collaboration() {
		name = new String();
		roles = new ArrayList<CD_Role>();
	}
	
	public CD_Collaboration(String name, ArrayList<CD_Role> roles) {
		this.name = name;
		this.roles = roles;
	}

	public void setName(String name) {
		this.name = name;
	}

	public String getName() {
		return name;
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

}
