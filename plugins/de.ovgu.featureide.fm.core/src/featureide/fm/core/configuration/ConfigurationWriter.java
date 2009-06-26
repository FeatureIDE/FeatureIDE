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
package featureide.fm.core.configuration;

import java.io.ByteArrayInputStream;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.Set;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.CoreException;

import featureide.fm.core.Feature;



public class ConfigurationWriter {

	private Configuration configuration;
	
	public static boolean userdefineorder = false;

	public ConfigurationWriter(Configuration configuration) {
		this.configuration = configuration;
	}
	
	public void saveToFile(IFile file) throws CoreException {
		InputStream source;
		StringBuffer buffer = new StringBuffer();
		if(userdefineorder){
			FeatureOrderReader reader = new FeatureOrderReader( ((IFile) file.getAdapter(IFile.class)).getProject().getLocation().toFile());
			//source = new ByteArrayInputStream(reader.featureOrderRead().toString().getBytes());
			ArrayList<String> list = reader.featureOrderRead();
			Set<Feature> featureset = configuration.getSelectedFeatures();
			for(String s:list){
				for(Feature f: featureset){
					if(f.isLayer()){
						if(f.getName().equals(s))
						buffer.append(s+"\r\n");
					}
				}
			}
			
			source = new ByteArrayInputStream(buffer.toString().getBytes());
		}
			
		else{	
			source = new ByteArrayInputStream(writeIntoString().getBytes());
		
		}
		if (file.exists()) {
			file.setContents(source, false, true, null);
		}
		else {
			file.create(source, false, null);
		}	
	}

	public String writeIntoString() {
		StringBuffer out = new StringBuffer();
		writeSelectedFeatures(configuration.getRoot(), out);	
		return out.toString();
	}

	private void writeSelectedFeatures(SelectableFeature feature, StringBuffer out) {
		if (feature.getFeature().isLayer() && feature.getSelection() == Selection.SELECTED)
			out.append(feature.getName() + "\r\n");
		for (TreeElement child : feature.getChildren())
			writeSelectedFeatures((SelectableFeature) child, out);
	}
	
}
