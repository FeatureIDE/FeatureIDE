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
package de.ovgu.featureide.featurecpp.wrapper;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;

import de.ovgu.featureide.featurecpp.FeatureCppCorePlugin;

/**
 * 
 * TODO description
 * 
 * @author Tom Brosch
 */
public class FeatureCppWrapper {
	
	final String featureCppExecutableName;
	String sourceDirectory = null;
	String outputDirectory = null;
	
	public FeatureCppWrapper(String featureCppExecutablePath) {
		this.featureCppExecutableName = featureCppExecutablePath;
	}
	
	public void initialize(IFolder sourceFolder, IFolder outputFolder) {
		this.sourceDirectory = sourceFolder.getRawLocation().toOSString();
		this.outputDirectory = outputFolder.getRawLocation().toOSString();
	}
	
	public void compose(IFile equation) {
		FeatureCppCorePlugin.getDefault().logInfo("Fcpp: composing");
		assert(equation != null && equation.exists()) : "Equation file does not exist";
		ProcessBuilder processBuilder = new ProcessBuilder(new String[] {
				featureCppExecutableName, "-o=" + outputDirectory, "-s=" + sourceDirectory, "-gpp",
				equation.getRawLocation().toOSString()
		});
		try {
			Process process = processBuilder.start();
			process.waitFor();
			BufferedReader reader = new BufferedReader(new InputStreamReader(process.getInputStream()));
			String line = null;
			while((line=reader.readLine()) != null) {
				FeatureCppCorePlugin.getDefault().logInfo(line);
			}
			
		} catch (IOException e) {
			FeatureCppCorePlugin.getDefault().logError(e);
		} catch (InterruptedException e) {
			FeatureCppCorePlugin.getDefault().logError(e);
		}
	}
}
