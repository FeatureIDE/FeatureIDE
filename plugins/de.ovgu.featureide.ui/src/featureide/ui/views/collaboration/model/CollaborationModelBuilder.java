/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2010  FeatureIDE Team, University of Magdeburg
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
package featureide.ui.views.collaboration.model;

import org.eclipse.core.resources.IFolder;
import org.eclipse.core.runtime.IPath;

import featureide.core.IFeatureProject;
import featureide.core.jakprojectmodel.IClass;
import featureide.core.jakprojectmodel.IFeature;
import featureide.core.jakprojectmodel.IJakModelElement;
import featureide.core.jakprojectmodel.IJakProjectModel;

/**
 * This CollaborationModelBuilder builds the CollaborationModel with the help of JakProjectModel.
 * 
 * @author Constanze Adler
 */
public class CollaborationModelBuilder {
	private CollaborationModel model;
	
	public CollaborationModelBuilder(){
		model = new CollaborationModel();
	}
	
	public CollaborationModel buildCollaborationModel(IFeatureProject featureProject){
		model.classes.clear();
		model.roles.clear();
		model.collaborations.clear();
		IJakProjectModel jakProject = featureProject.getJakProjectModel();
		IFolder path = null;
		
		IFeature[] features = null;
		if (jakProject == null) return null;
		features = jakProject.getFeatures();
		if (features == null) return null;
		path = featureProject.getSourceFolder();
		
		for (IFeature f : features){
			
			Collaboration coll = new Collaboration(f.getName());
			IJakModelElement[] element = f.getChildren();
			if (element instanceof IClass[]){
				for (IClass c : (IClass[]) element){
					IPath pathToFile = path.getFullPath();
					pathToFile = pathToFile.append(f.getName());
					pathToFile = pathToFile.append(c.getName());
				
					
					String name = c.getName();
					Role r = new Role(name);
					r.setPath(pathToFile);
					name = (name.split("[.]"))[0];
					Class cl = new Class(name);
					if (model.classes.containsKey(cl.getName())){
						r.setParentClass(model.classes.get(cl.getName()));
					}
					else{	
						r.setParentClass(cl);
						model.classes.put(cl.getName(),cl);
					}
					r.setCollaboration(coll);
					model.roles.add(r);
				}
			}
			model.collaborations.add(coll);		
		}	 
		
		
		
		
		return model;
	}


}
