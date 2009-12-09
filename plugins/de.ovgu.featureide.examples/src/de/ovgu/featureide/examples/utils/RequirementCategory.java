/*****************************************************************************************
*   Copyright © 2004 by Robert Schrenk. All rights are reserved.                         *
*                                                                                        *
*   If you like this code then feel free to go ahead and use it.                         *
*   The only thing I ask is that you don't remove or alter my copyright notice.          *
*                                                                                        *
*   Your use of this software is entirely at your own risk. I make no claims or          *
*   warrantees about the reliability or fitness of this code for any particular purpose. *
*   If you make changes or additions to this code please mark your code as being yours.  *
*****************************************************************************************/

package de.ovgu.featureide.examples.utils;

import java.util.HashMap;
import java.util.Map;
import java.util.Set;

public class RequirementCategory
{
	String catName;
	Map<String, String>  requirements = new HashMap<String, String>();
	
	public RequirementCategory (String categoryName, Map<String, String>  requirements) {
		this.catName = categoryName;
		this.requirements = requirements;		
	}
	
	public String getCategory() {
		return catName;
	}
	
	public Set<String> getPluginIds() {
		return requirements.keySet();
	}
	
	public String getErrorMsg(String pluginId) {
		return requirements.get(pluginId);
	
	}
}