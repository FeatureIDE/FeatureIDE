package de.ovgu.featureide.core.runtime;

import java.io.BufferedReader;
import java.io.ByteArrayInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.UnsupportedEncodingException;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.HashMap;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;

import de.ovgu.featureide.core.runtime.activator.RuntimeCorePlugin;
import de.ovgu.featureide.fm.core.FMComposerExtension;

/**
 * Class for handling renaming events of features within the model.
 * 
 * @author Kai Wolf
 * @author Matthias Quaas
 *
 */
public class RuntimeFMComposerExtension extends FMComposerExtension {

	public RuntimeFMComposerExtension() {

	}

	@Override
	protected boolean isValidFeatureNameComposerSpecific(String s) {
		return super.isValidFeatureNameComposerSpecific(s);
	}

	@Override
	public String getOrderPageMessage() {
		return super.getOrderPageMessage();
	}

	@Override
	public boolean hasFeaureOrder() {
		return true;
	}

	/**
	 * Actual handling of renaming.
	 */
	@Override
	public boolean performRenaming(String oldName, String newName, IProject project) {

		ArrayList<FeatureLocation> locations = new ArrayList<FeatureLocation>();
		
		//get FeatureLocation objects with the given oldName as feature name 
		for (FeatureLocation loc : RuntimeComposer.featureLocs) {
			if (loc.getFeatureName().equals(oldName)) {
				locations.add(loc);
			}
		}
		//only load and parse each class file once
		HashMap<String, String[]> processedClassFiles = new HashMap<String, String[]>();

		for (FeatureLocation loc : locations) {
			String[] oldClassStringArray = null;
			String classPath = loc.getOSPath();
			int lineNumber = loc.getStartLineNum();

			//if the class has not already been loaded, load it
			if (!processedClassFiles.containsKey(classPath)) {

				try {
					IFile classFile = loc.getClassFile();
					InputStream oldClassStream = classFile.getContents();

					StringBuilder inputStringBuilder = new StringBuilder();
					BufferedReader bufferedReader = null;

					bufferedReader = new BufferedReader(new InputStreamReader(oldClassStream, "UTF-8"));

					String line = bufferedReader.readLine();
					while (line != null) {
						inputStringBuilder.append(line);
						inputStringBuilder.append('\n');
						line = bufferedReader.readLine();
					}
					oldClassStringArray = inputStringBuilder.toString().split("\\n");
					processedClassFiles.put(classPath, oldClassStringArray);

				} catch (UnsupportedEncodingException e) {
					RuntimeCorePlugin.getDefault().logError(e);
				} catch (IOException e) {
					RuntimeCorePlugin.getDefault().logError(e);
				} catch (CoreException e) {
					RuntimeCorePlugin.getDefault().logError(e);
				}
			//else use the one in the map
			} else {
				oldClassStringArray = processedClassFiles.get(classPath);
			}
			oldClassStringArray[lineNumber - 1] = oldClassStringArray[lineNumber - 1].replace(
					RuntimeComposer.GET_PROPERTY_METHOD + "(\"" + oldName + "\")",
					RuntimeComposer.GET_PROPERTY_METHOD + "(\"" + newName + "\")");

			final StringBuilder newClassString = new StringBuilder();
			for (int i = 0; i < oldClassStringArray.length; i++) {
				if (i != 0) {
					newClassString.append(System.lineSeparator());
				}
				newClassString.append(oldClassStringArray[i]);
			}

			InputStream newClassStream = new ByteArrayInputStream(newClassString.toString().getBytes(StandardCharsets.UTF_8));
			try {
				loc.getClassFile().setContents(newClassStream, IFile.FORCE, null);
			} catch (CoreException e) {
				RuntimeCorePlugin.getDefault().logError(e);
			}
			loc.setFeatureName(newName);
		}

		return true;

	}

	@Override
	public String getErroMessage() {
		return super.getErroMessage();
	}

}
