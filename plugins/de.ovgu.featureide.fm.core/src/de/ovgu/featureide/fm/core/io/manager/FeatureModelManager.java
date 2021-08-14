/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2019  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.fm.core.io.manager;

import java.io.File;
import java.io.IOException;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;

import javax.annotation.CheckForNull;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IWorkspace;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.IPath;

import de.ovgu.featureide.fm.core.FeatureModelAnalyzer;
import de.ovgu.featureide.fm.core.Logger;
import de.ovgu.featureide.fm.core.analysis.cnf.formula.FeatureModelFormula;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.IEventListener;
import de.ovgu.featureide.fm.core.base.impl.FMFactoryManager;
import de.ovgu.featureide.fm.core.base.impl.FMFormatManager;
import de.ovgu.featureide.fm.core.io.IFeatureModelFormat;
import de.ovgu.featureide.fm.core.io.IPersistentFormat;

/**
 * Responsible to load and save all information for a feature model instance.
 *
 * @author Sebastian Krieter
 */
public class FeatureModelManager extends AFileManager<IFeatureModel> implements IFeatureModelManager {

	public static final int CHANGE_ALL = 0;
	public static final int CHANGE_DEPENDENCIES = 1;
	public static final int CHANGE_ATTRIBUTES = 2;
	public static final int CHANGE_ORDER = 3;
	public static final int CHANGE_GRAPHICS = 4;
	public static final int CHANGE_MODEL_PROPERTY = 5;
	public static final int CHANGE_NOTHING = Integer.MAX_VALUE;

	private FeatureModelFormula persistentFormula = null;
	private FeatureModelFormula variableFormula = null;

	@CheckForNull
	public static FeatureModelManager getInstance(Path path) {
		return getOrCreateInstance(path, FeatureModelManager.class, null);
	}

	public static boolean isFileSupported(Path filePath) {
		return FMFormatManager.getInstance().hasFormat(filePath);
	}

	public static IFeatureModelManager getInstance(IFeatureModel featureModel) {
		final IFeatureModelManager featureModelManager = getInstance(featureModel.getSourceFile());
		return (featureModelManager == null) ? new VirtualFeatureModelManager(featureModel) : featureModelManager;
	}

	public static final IFeatureModel load(Path path) {
		return FeatureModelIO.getInstance().load(path);
	}

	public static FileHandler<IFeatureModel> getFileHandler(Path path) {
		return FeatureModelIO.getInstance().getFileHandler(path);
	}

	public static final boolean save(IFeatureModel featureModel, Path path, IPersistentFormat<IFeatureModel> format) {
		return FeatureModelIO.getInstance().save(featureModel, path, format);
	}

	protected Object undoContext = null;

	/**
	 * importers is a list of all listeners that need to be updated when the feature model managed through this model is changed.
	 */
	private final List<IEventListener> importers;

	protected FeatureModelManager(Path identifier) {
		super(identifier, FMFormatManager.getInstance(), FMFactoryManager.getInstance());
		importers = new ArrayList<>();
	}

	@Override
	protected boolean init(IPersistentFormat<IFeatureModel> desiredFormat) {
		if (super.init(desiredFormat)) {
			variableObject.setSourceFile(getPath());
			return true;
		}
		return false;
	}

	@Override
	public IFeatureModelFormat getFormat() {
		return (IFeatureModelFormat) super.getFormat();
	}

	@Override
	protected IFeatureModel copyObject(IFeatureModel oldObject) {
		final IFeatureModel clone = oldObject.clone();
		clone.setEventManager(this);
		return clone;
	}

	@Override
	public FeatureModelFormula getPersistentFormula() {
		if (persistentFormula == null) {
			persistentFormula = new FeatureModelFormula(persistentObject);
		}
		return persistentFormula;
	}

	@Override
	public FeatureModelFormula getVariableFormula() {
		fileOperationLock.lock();
		try {
			if (variableFormula == null) {
				variableFormula = new FeatureModelFormula(getSnapshot());
			}
			return variableFormula;
		} finally {
			fileOperationLock.unlock();
		}
	}

	@Override
	protected void resetSnapshot(int changeIndicator) {
		super.resetSnapshot(changeIndicator);
		if (variableFormula != null) {
			if (changeIndicator <= CHANGE_DEPENDENCIES) {
				variableFormula = null;
			} else if (changeIndicator == CHANGE_MODEL_PROPERTY) {
				// Not nessessary to rebuild the variable formula, just copy the properties to the variable formula's model
				variableFormula.getFeatureModel().getProperty().setProperties(variableObject.getProperty().getProperties());
			}
		}
	}

	@Override
	protected void setPersistentObject(IFeatureModel persistentObject) {
		super.setPersistentObject(persistentObject);
		persistentFormula = null;
	}

	@Override
	protected void setVariableObject(IFeatureModel variableObject) {
		if (this.variableObject != null) {
			for (final IEventListener listener : this.variableObject.getListeners()) {
				variableObject.addListener(listener);
			}
		}
		fileOperationLock.lock();
		try {
			super.setVariableObject(variableObject);
		} finally {
			fileOperationLock.unlock();
		}
	}

	@Override
	protected IFeatureModel createObject() throws Exception {
		final IFeatureModel featureModel = super.createObject();
		featureModel.setSourceFile(getPath());
		featureModel.setEventManager(this);
		return featureModel;
	}

	@Override
	public Object getUndoContext() {
		return undoContext;
	}

	@Override
	public void setUndoContext(Object undoContext) {
		this.undoContext = undoContext;
	}

	public static FeatureModelAnalyzer getAnalyzer(IFeatureModel fm) {
		return new FeatureModelAnalyzer(new FeatureModelFormula(fm));
	}

	/**
	 * Adds an listener that imports this feature model.
	 *
	 * @param listener - {@link IEventListener}
	 */
	public void addImportListener(IEventListener listener) {
		importers.add(listener);
	}

	/**
	 * Removes this listener from the import list.
	 *
	 * @param e - {@link IEventListener}
	 */
	public void removeImportListener(IEventListener e) {
		importers.remove(e);
	}

	/**
	 * Removes all listeners from the import list. Call this method when the feature model is closed and its changes need not to be propagated to (still opened)
	 * importers anymore.
	 */
	public void removeAllListeners() {
		importers.clear();
	}

	@Override
	public void informImports(FeatureIDEEvent e) {

		// Für jeden Listener möchte man überprüfen, ob sich dieser auf ein Feature Modell bezieht, welches genau das Modell importiert, welches dieser
		// FeatureModelManager verwaltet.

		for (final IEventListener i : importers) {
			i.propertyChange(e);
		}
	}

	/**
	 * Looks up the project-relative Eclipse path for the given Java file. With this method, we may get the project of a feature model file, for example.
	 *
	 * @param file - {@link File}
	 * @return an {@link IProject} for the project file is contained in, or null otherwise.
	 */
	public static IPath getProject(File file) {
		final IWorkspace workspace = ResourcesPlugin.getWorkspace();
		try {
			final IPath path = org.eclipse.core.runtime.Path.fromOSString(file.getCanonicalPath());
			final IFile fileForPath = workspace.getRoot().getFileForLocation(path);
			if ((null == fileForPath) || !fileForPath.exists()) {
				return null;
			}
			return fileForPath.getFullPath();
		} catch (final IOException e) {
			Logger.logError(e);
			return null;
		}
	}

}
