/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2009  FeatureIDE Team, University of Magdeburg
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program. If not, see http://www.gnu.org/licenses/.
 *
 * See http://www.fosd.de/featureide/ for further information.
 */
package featureide.core.jakprojectmodel.internal;

import java.util.HashMap;
import java.util.LinkedList;

import mixin.AST_Program;

import org.eclipse.core.resources.IFile;

import featureide.core.jakprojectmodel.IClass;
import featureide.core.jakprojectmodel.IFeature;
import featureide.core.jakprojectmodel.IJakElement;
import featureide.core.jakprojectmodel.IJakProject;

/** 
 * The model of a jak project 
 * 
 * @author Tom Brosch
 *
 */
public class JakProject extends JakElement implements IJakProject {
	
	private HashMap<IFile, Class> classesMap;
	private HashMap<String,Class> classes;
	private String projectName;
	
	/**
	 * Creates a new instance of a jak project
	 * 
	 * @param name		Name of the project
	 */
	public JakProject(String name) {
		classesMap = new HashMap<IFile, Class>();
		classes = new HashMap<String,Class>();
		projectName = name;
	}
	
	/* (non-Javadoc)
	 * @see featureide.core.jakprojectmodel.IJakProject#getNumberOfSelectedFeatures()
	 */
	public int getNumberOfSelectedFeatures() {
		return 0;
	}
	
	/* (non-Javadoc)
	 * @see featureide.core.jakprojectmodel.IJakProject#getSelectedFeatures()
	 */
	public IFeature[] getSelectedFeatures() {
		return null;
	}
	
	/* (non-Javadoc)
	 * @see featureide.core.jakprojectmodel.IJakProject#getNumberOfFeatures()
	 */
	public int getNumberOfFeatures() {
		return 0;
	}
	
	/* (non-Javadoc)
	 * @see featureide.core.jakprojectmodel.IJakProject#getFeatures()
	 */
	public IFeature[] getFeatures() {
		return null;
	}
	
	/* (non-Javadoc)
	 * @see featureide.core.jakprojectmodel.IJakProject#getFeature(java.lang.String)
	 */
	public IFeature getFeature(String featureName) {
		return null;
	}
	
	/* (non-Javadoc)
	 * @see featureide.core.jakprojectmodel.IJakProject#getNumberOfClasses()
	 */
	public int getNumberOfClasses() {
		return classesMap.size();
	}
	
	/* (non-Javadoc)
	 * @see featureide.core.jakprojectmodel.IJakProject#getClasses()
	 */
	public IClass[] getClasses() {
		IClass[] classArray = new Class[classes.size()];
		int pos = 0;
		for( IClass c: classes.values() ) {
			classArray[pos++] = c;
		}
		return classArray;
	}
	
	/* (non-Javadoc)
	 * @see featureide.core.jakprojectmodel.IJakProject#getClass(org.eclipse.core.resources.IFile)
	 */
	public IClass getClass(IFile file) {
		if( !classesMap.containsKey(file) )
			return null;
		IClass c = classesMap.get(file);
		c.setJakfile(file);
		return c;
	}
	
	public String getName() {
		return projectName;
	}
	
	public IJakElement[] getChildren() {
		return getClasses();
	}
	
	public boolean hasChildren() {
		return getNumberOfClasses() > 0;
	}
	
	/* (non-Javadoc)
	 * @see featureide.core.jakprojectmodel.IJakProject#addClass(java.lang.String, java.util.Vector, mixin.AST_Program[], mixin.AST_Program[])
	 */
	public void addClass(String className, LinkedList<IFile> sources, AST_Program[] composedASTs, AST_Program[] ownASTs) {
		Class currentClass = null;
		
		// Parse the name and the ownASTs to know to which IFiles this class file belongs to
		
		// This class doesnt exist, than create a new class object
		if( classes.containsKey(className) ) {
			currentClass = classes.get(className);
		} else {
			currentClass = new Class(className);
			classes.put(className, currentClass);
		}
		
		for( int i = 0; i < sources.size(); i++ ) {
			if( !classesMap.containsKey(sources.get(i)) )
				classesMap.put(sources.get(i), currentClass);
		}
		try {
			currentClass.updateAst(sources, composedASTs, ownASTs);
		} catch(Throwable e) {
			e.printStackTrace();
		}
	}
}
