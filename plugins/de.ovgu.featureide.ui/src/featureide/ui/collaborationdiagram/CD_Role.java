package featureide.ui.collaborationdiagram;

import java.util.ArrayList;

public class CD_Role {

	/**
	 * the name of this role; composed of the feature and class it belongs to
	 */
	private String name;

	/**
	 * the content of this role, e.g. the method definition
	 */
	private ArrayList<String> content;

	public CD_Role() {
		name = new String();
		content = new ArrayList<String>();
	}

	public CD_Role(String name, ArrayList<String> content) {
		this.name = name;
		this.content = content;
	}

	public void setName(String name) {
		this.name = name;
	}

	public String getName() {
		return name;
	}

	public void setContent(ArrayList<String> content) {
		this.content = content;
	}

	public ArrayList<String> getContent() {
		return content;
	}

}
