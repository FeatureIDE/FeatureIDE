/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2016  FeatureIDE team, University of Magdeburg, Germany
 *
 * This file is part of FeatureIDE.
 * 
 * FeatureIDE is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * FeatureIDE is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with FeatureIDE.  If not, see <http://www.gnu.org/licenses/>.
 *
 * See http://featureide.cs.ovgu.de/ for further information.
 */
package de.ovgu.featureide.refactoring.typesystem;

import java.io.File;
import java.net.URI;
import java.util.HashMap;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.Path;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.builder.FeatureProjectNature;
import de.ovgu.featureide.refactoring.RefactoringPlugin;
import de.ovgu.featureide.refactoring.parser.LoopException;
import de.ovgu.featureide.refactoring.parser.Parser;
import de.ovgu.featureide.refactoring.windows.ErrorWindow;

import refactor.TypeSystem;

/**
 * Represents if a type system is up-to-date.
 * 
 * @author Stephan Kauschka
 */
class TypeSystemStatus {
	public TypeSystem ts;
	public boolean updateNeeded;
	public IFile equationFile;

	public TypeSystemStatus(TypeSystem typeSys, boolean update, IFile eqFile) {
		ts = typeSys;
		updateNeeded = update;
		equationFile = eqFile;
	}
}

/**
 * Handles the type systems for FeatureIDE projects owning Jak files.
 * 
 * @author Stephan Kauschka
 */
public class TypeSystemManager {

	private static final HashMap<URI, TypeSystemStatus> TYPESYSTEMS = new HashMap<URI, TypeSystemStatus>();

	private TypeSystemManager() {
	}

	/**
	 * Returns the corresponding typesystem for a FeatureIDE-Project. If the
	 * given ProjectLocationURI does not belong to a FeatureIDE-Project null is
	 * returned. If the typesystem for the FeatureIDE-Project does not exist it
	 * will be created with the currently used equation[s]-file of this project.
	 */
	public static TypeSystem getTypesystem(URI projectLocationURI) {

		if (!isFeatureIDEProject(projectLocationURI))
			return null;

		if (exists(projectLocationURI)) {
			if (needsUpdate(projectLocationURI)) {
				refreshTypesystem(projectLocationURI);
			}
			TypeSystem ts = TYPESYSTEMS.get(projectLocationURI).ts;
			return ts;
		}

		Path p = new Path(projectLocationURI.getPath());
		IResource res = ResourcesPlugin.getWorkspace().getRoot()
				.getContainerForLocation(p);
		IFile file = CorePlugin.getFeatureProject(res).getCurrentConfiguration();
		TypeSystem t = new TypeSystem();
		TYPESYSTEMS.put(projectLocationURI,
				new TypeSystemStatus(t, false, file));

		initializeTypesystem(projectLocationURI);
		return t;
	}

	/**
	 * Returns the corresponding typesystem for a FeatureIDE-Project and a given
	 * equation[s]-file. If the given ProjectLocationURI does not belong to a
	 * FeatureIDE-Project null is returned. If the typesystem for the
	 * FeatureIDE-Project does not exist it will be created with the given
	 * equation[s]-file.
	 */
	public static TypeSystem getTypesystem(URI projectLocationURI,
			IFile equationsFile) {

		if (!isFeatureIDEProject(projectLocationURI))
			return null;
		if (exists(projectLocationURI)) {
			setEquationFile(projectLocationURI, equationsFile);
			if (needsUpdate(projectLocationURI)) {
				refreshTypesystem(projectLocationURI);
			}
			TypeSystem ts = TYPESYSTEMS.get(projectLocationURI).ts;
			return ts;
		}

		TypeSystem t = new TypeSystem();
		TYPESYSTEMS.put(projectLocationURI, new TypeSystemStatus(t, false,
				equationsFile));
		initializeTypesystem(projectLocationURI);
		return t;
	}

	/**
	 * Initializes the corresponding typesystem for a FeatureIDE-Project by
	 * parsing the given equation[s]-file and loading the layers specified
	 * inside this file. If possible, the necessary AST's are taken from the
	 * FeatureIDE-PlugIn, else they are created by the typesystem.
	 */
	@SuppressWarnings("unused")
	private static boolean initializeTypesystem(URI projectLocationURI) {
		TypeSystem typeSystem = TYPESYSTEMS.get(projectLocationURI).ts;
		IFile eqFile = TYPESYSTEMS.get(projectLocationURI).equationFile;
		typeSystem.reset();
		Parser parser = null;

		try {
			// boolean astExisting = false;
			// //check whether the AST's can be taken from the Core-PlugIn
			// IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
			// IContainer[] con =
			// root.findContainersForLocationURI(projectLocationURI);
			// if(con==null || con.length==0)
			// throw new
			// Exception("could not find the corresponding IResource for " +
			// projectLocationURI);
			// IFeatureProject featPrj = CorePlugin.getProjectData(con[0]);
			// IJakProject jakPrj = featPrj.getJakProject();
			// if(jakPrj.hasChildren())
			// astExisting = true;
			//
			// //if possible get the AST's from the Core-PlugIn
			// HashMap<File,program> astMap = new HashMap<File,program>();
			// if(astExisting){
			// IClass[] classes = jakPrj.getClasses();
			// for(int i=0; i<classes.length; i++){
			// AST_Program[] objs = classes[i].getASTs();
			// LinkedList<IFile> iFiles = classes[i].getSources();
			//
			// for(int j=0; j<iFiles.size(); j++){
			// //adapt the AST to fit the requirements for the typesystem
			// //(that is delete the node in the AST that contains the source
			// //information, which can't be handled by the typesystem)
			// program p = (program)objs[j];
			// if (p.getAST_Class().arg[0].arg[0] instanceof SourceDecl){
			// // p = (program) p.clone();
			// // p.getAST_Class().arg[0].Delete();
			// }
			// File file = iFiles.get(j).getLocation().toFile();
			// astMap.put(file, p);
			// }
			// }
			// }

			parser = new Parser(eqFile);
			try {
				int numberOfPrograms = parser.getNumberOfPrograms();
				int numberOfLayer = 0;

				for (int program = 1; program <= numberOfPrograms; program++) {
					numberOfLayer = parser.getNumberOfLayers(program);

					for (int layer = 1; layer <= numberOfLayer; layer++) {
						String[] filePaths = parser.extractJakFilePaths(
								program, layer).toArray(new String[] {});
						File[] files = new File[filePaths.length];

						for (int i = 0; i < filePaths.length; i++) {
							files[i] = new File(filePaths[i]);
						}

						// //if possible get the AST's for the jak-files in
						// "File[] files" from the Core-PlugIn
						// if(astExisting){
						// program[] asts = new program[files.length];
						// for(int i=0; i<files.length; i++){
						// asts[i] = (program) astMap.get(files[i]);
						// }
						// typeSystem.addLayer(files,asts);
						// }
						// else
						// typeSystem.addLayer(files);
						typeSystem.addLayer(files, parser.getLayerName(program,
								layer), eqFile.getParent().getParent()
								.getLocation().toOSString()
								+ Parser.FILESEPARATOR
								+ Parser.FILESRC
								+ Parser.FILESEPARATOR
								+ parser.getLayerName(program, layer));
					}
				}
			} catch (Exception e) {
				new ErrorWindow(e.getClass().getSimpleName(),
						"The typesystem could not be created due to the following reason:\n\n"
								+ e.getMessage());
				parser.releaseResources();
				remove(projectLocationURI);
				return false;
			}
			parser.releaseResources();
			setNeedsUpdate(projectLocationURI, false);

		} catch (LoopException e) {
			new ErrorWindow("LoopException",
					"A LoopException occured while parsing program "
							+ e.getErrorOffset() + " in " + eqFile.getName()
							+ ".");
			if (parser != null)
				parser.releaseResources();
			RefactoringPlugin.getDefault().openEditor(
					"org.eclipse.ui.DefaultTextEditor", eqFile);
			return false;
		} catch (Exception e) {
			new ErrorWindow(e.getClass().getSimpleName(),
					"An Exception occured while parsing the equation(s)-file:\n"
							+ e.getMessage());
			if (parser != null)
				parser.releaseResources();
			RefactoringPlugin.getDefault().openEditor(
					"org.eclipse.ui.DefaultTextEditor", eqFile);
			return false;
		}

		return true;
	}

	/**
	 * Refreshes the corresponding typesystem for a FeatureIDE-Project by
	 * parsing the equation[s]-file associated with it and loading the layers
	 * specified inside this file.
	 */
	public static boolean refreshTypesystem(URI projectLocationURI) {
		if (exists(projectLocationURI)) {
			return initializeTypesystem(projectLocationURI);
		}
		return false;
	}

	/**
	 * Checks whether the corresponding Typesystem for a FeatureIDE-Project has
	 * been created.
	 */
	public static boolean exists(URI projectLocationURI) {
		return TYPESYSTEMS.containsKey(projectLocationURI);
	}

	/**
	 * Checks whether a given URI belongs to a FeatureIDE-Project.
	 */
	public static boolean isFeatureIDEProject(URI projectLocationURI) {
		IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
		IContainer[] con = root
				.findContainersForLocationURI(projectLocationURI);
		if (con == null || con.length == 0)
			return false;
		if (con[0].getType() != IResource.PROJECT)
			return false;
		try {
			if (((IProject) con[0]).hasNature(FeatureProjectNature.NATURE_ID))
				return true;
		} catch (Exception e) {
		}
		return false;
	}

	/**
	 * Deletes the Typesystem of a FeatureIDE-Project. If the URI to be removed
	 * does not exists false is returned.
	 */
	public static boolean remove(URI projectLocationURI) {
		if (exists(projectLocationURI)) {
			TYPESYSTEMS.get(projectLocationURI).ts.delete();
			TYPESYSTEMS.remove(projectLocationURI);
			return true;
		}
		return false;
	}

	/**
	 * Checks whether the typesystem of a FeatureIDE-project has to be updated.
	 * This is the case when the currently used equation[s]-file or any jak-file
	 * of the project has changed.
	 */
	private static boolean needsUpdate(URI projectLocationURI) {
		if (!exists(projectLocationURI))
			return false;
		TypeSystemStatus tss = TYPESYSTEMS.get(projectLocationURI);
		return tss.updateNeeded;
	}

	/**
	 * Sets whether the Typesystem of a FeatureIDE-Project has to be updated.
	 * This is the case when the current equation of the Project or any Jak-File
	 * of the Project has changed.
	 */
	public static void setNeedsUpdate(URI projectLocationURI,
			boolean needsUpdate) {
		if (exists(projectLocationURI)) {
			TYPESYSTEMS.get(projectLocationURI).updateNeeded = needsUpdate;
		}
	}

	/**
	 * Returns the equation-file which is used to create the typesystem
	 * corresponding to the given FeatureIDE-Project. If the project does not
	 * exist null is returned.
	 */
	public static IFile getEquationFile(URI projectLocationURI) {
		if (exists(projectLocationURI)) {
			return TYPESYSTEMS.get(projectLocationURI).equationFile;
		}
		return null;
	}

	/**
	 * Sets the equation-file which is used to create the typesystem
	 * corresponding to the given FeatureIDE-Project.
	 */
	public static void setEquationFile(URI projectLocationURI,
			IFile equationFile) {
		if (exists(projectLocationURI)) {
			TYPESYSTEMS.get(projectLocationURI).equationFile = equationFile;
			setNeedsUpdate(projectLocationURI, true);
		}
	}

	/**
	 * Replaces the URI associated with a typesystem. If the URI to be replaced
	 * does not exist, false is returned.
	 */
	public static boolean replace(URI oldUri, URI newUri) {
		if (exists(oldUri)) {
			TypeSystemStatus tss = TYPESYSTEMS.get(oldUri);
			TYPESYSTEMS.put(newUri, tss);
			TYPESYSTEMS.remove(oldUri);
			return true;
		}
		return false;
	}

}
