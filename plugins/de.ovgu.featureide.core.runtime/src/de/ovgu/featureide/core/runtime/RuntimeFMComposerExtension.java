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

import de.ovgu.featureide.core.runtime.RuntimeComposer.FeatureLocation;
import de.ovgu.featureide.core.runtime.activator.RuntimeCorePlugin;
import de.ovgu.featureide.fm.core.FMComposerExtension;

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

	@Override
	public boolean performRenaming(String oldName, String newName, IProject project) {
		ArrayList<FeatureLocation> locations = new ArrayList<RuntimeComposer.FeatureLocation>();
	
		for (FeatureLocation loc : RuntimeComposer.featureLocs) {
			if (loc.getFeatureName().equals(oldName)) {
				locations.add(loc);
			}
		}

		HashMap<String, String[]> readClassFiles = new HashMap<String, String[]>();

		for (FeatureLocation loc : locations) {
			String[] oldClassString=null;
			String classPath = loc.getClassFile().getFullPath().toOSString();
			int lineNumber = loc.getStartLineNum();

			if (!readClassFiles.containsKey(classPath)) {

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
					oldClassString = inputStringBuilder.toString().split("\\n");
					readClassFiles.put(classPath, oldClassString);

					oldClassString=replace(oldClassString, lineNumber, oldName, newName);
				
				} catch (UnsupportedEncodingException e) {
					RuntimeCorePlugin.getDefault().logError(e);
				} catch (IOException e) {
					RuntimeCorePlugin.getDefault().logError(e);
				} catch (CoreException e) {
					RuntimeCorePlugin.getDefault().logError(e);
				}
			} else {
				oldClassString=replace(readClassFiles.get(classPath), lineNumber, oldName, newName);
			}
			
			String newClassString = String.join("\n", oldClassString);
			
			InputStream newClassStream = new ByteArrayInputStream(newClassString.getBytes(StandardCharsets.UTF_8));
			try {
				loc.getClassFile().setContents(newClassStream, IFile.FORCE, null);
			} catch (CoreException e) {
				RuntimeCorePlugin.getDefault().logError(e);
			}
			loc.setFeatureName(newName);
		}

		return true;

	}

	private String[] replace(String[] classString, int lineNumber, String oldName, String newName) {

		classString[lineNumber-1] = classString[lineNumber-1].replace("getProperty(\""+oldName+"\")", "getProperty(\""+newName+"\")"); 
		return classString;
	}

	@Override
	public String getErroMessage() {
		return super.getErroMessage();
	}

}
