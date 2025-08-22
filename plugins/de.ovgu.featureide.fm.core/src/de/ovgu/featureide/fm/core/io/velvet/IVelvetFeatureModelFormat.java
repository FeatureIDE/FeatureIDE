package de.ovgu.featureide.fm.core.io.velvet;

import java.io.File;
import java.io.IOException;

import org.eclipse.core.resources.IProject;

import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.impl.MultiFeatureModel;
import de.ovgu.featureide.fm.core.io.ProblemList;

public interface IVelvetFeatureModelFormat {

	public boolean supportsRead();

	public boolean supportsWrite();

	public String write(IFeatureModel object);

	public ProblemList read(IFeatureModel object, CharSequence source);

	public String getSuffix();

	public String getId();

	public String getName();

	public boolean initExtension();

	public String getExtFeatureModelName();

	public MultiFeatureModel getExtFeatureModel();

	/**
	 * @param text
	 */
	public void setExtFeatureModelName(String name);

	/**
	 * @return
	 */
	public File getFeatureModelFile();

	/**
	 * @return
	 */
	public boolean isVelvetImport();

	/**
	 * @return
	 */
	public boolean getLocalSearch();

	/**
	 * @return
	 */
	public boolean getIsUsedAsAPI();

	/**
	 * @return
	 */
	public String[] getPaths();

	/**
	 * @return
	 * @throws IOException
	 */
	public IProject getProject();

	/**
	 * @param modelName
	 * @return
	 */
}
