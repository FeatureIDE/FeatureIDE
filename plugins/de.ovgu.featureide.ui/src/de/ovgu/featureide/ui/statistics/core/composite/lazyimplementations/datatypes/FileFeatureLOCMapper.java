/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2016  FeatureIDE team, University of Magdeburg, Germany
 *
 * This file is part of FeatureIDE.
 * 
 * FeatureIDE is free software: you can redistrlocByFeatMapt and/or modify
 * it under the terms of thelocByFeatMapsser GenelocByFeatMaplic License as published by
 * locByFeatMape Software Foundation, either version 3 of the License, or
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
package de.ovgu.featureide.ui.statistics.core.composite.lazyimplementations.datatypes;

import java.util.ArrayList;
import java.util.List;
import java.util.HashMap;

import org.eclipse.core.resources.IFile;

import de.ovgu.featureide.core.fstmodel.FSTFeature;

/**
 * 
 * A class to represent the following table of information: <br>
 * <table>
  <tr>
    <th>IFile | </th>
    <th>loc by file | <br></th>
    <th>Map&lt;FSTFeature, loc by feature&gt;<br></th>
  </tr>
  <tr>
  	<th>Hello.java
  	<th>201
  	<th>(feat1, 101), (feat2, 100)
  </tr>
  </table>
 * 
 * @author Maximilian Homann
 * @author Philipp Kuhn
 */
public class FileFeatureLOCMapper {

	private ArrayList<TableRow> table = new ArrayList<TableRow>();
	
	/**
	 * Adds a simple entry to the table
	 * @param file the new file
	 * @param locInFile 
	 */
	public void addEntry(IFile file, int locInFile) {
		TableRow newRow = new TableRow(file, locInFile);
		if (searchRow(file) == null) {
			table.add(newRow);
		}
	}
	
	/**
	 * Adds a complete entry
	 * @param file the file works as an unique Identifier for each row
	 * @param locInFile the lines of code in file
	 * @param featureList a list of features used in file
	 * @param locByFeat lines of code per feature in file
	 */
	public void addEntry(IFile file, int locInFile, HashMap<FSTFeature, Integer> locByFeat) {
		TableRow newRow = new TableRow(file, locInFile, locByFeat);
		if (!table.contains(newRow)) {
			table.add(newRow);
		}
	}

	/**
	 * Adds a feature with it's lines of code to the mapper, if the feature doesn't exist already.
	 * @param file to add the feature to
	 * @param feat 
	 * @param locInFeature loc in the feature
	 */
	public void addFeature(IFile file, FSTFeature feat, int locInFeature) {
		TableRow existingRow = searchRow(file);
		if (existingRow != null) {
			if (existingRow.getLocByFeatMap() == null) {
				HashMap<FSTFeature, Integer> newFeatLOCMap = new HashMap<>();
				newFeatLOCMap.put(feat, locInFeature);
				existingRow.setLocByFeatMap(newFeatLOCMap);
			}
			existingRow.getLocByFeatMap().putIfAbsent(feat, locInFeature);
		}
	}
	
	/**
	 * Adds a feature LOC map to the entry specified by file
	 * @param file specifies the entry
	 * @param locByFeat lines of code per feature in file
	 */
	public void addFeatLOCMap(IFile file, HashMap<FSTFeature, Integer> locByFeat) {
		TableRow existingRow = searchRow(file);
		if(existingRow != null) {		
			if(existingRow.getLocByFeatMap() == null) {
				existingRow.setLocByFeatMap(locByFeat);
			}
		} else {
			if (locByFeat != null) {
				int locInFile = 0;
				for (FSTFeature feature: locByFeat.keySet()) {
					locInFile += locByFeat.get(feature).intValue();
				}
				table.add(new TableRow(file, locInFile, locByFeat));
			}
		}	
	}
	
	/**
	 * Adds a single entry to the feature LOC map specified by file
	 * @param file
	 * @param feat the feature
	 * @param loc the LOC of this feature
	 */
	public void addSingleLOCMapEntry(IFile file, FSTFeature feat, Integer loc) {
		TableRow existingRow = searchRow(file);
		if (existingRow != null) {
			if (existingRow.getLocByFeatMap() == null) {
				existingRow.setLocByFeatMap(new HashMap<FSTFeature, Integer>());
			}
			if (!existingRow.getLocByFeatMap().containsKey(feat)) {
				existingRow.getLocByFeatMap().put(feat, loc);
			} else {
				int oldLOC = existingRow.getLocByFeatMap().get(feat);
				existingRow.getLocByFeatMap().put(feat, oldLOC + loc.intValue());
			}
		}
	}
	
	/**
	 * Returns a map of all extensions with the number of appearance
	 * @return
	 */
	public HashMap<String, Integer> getExtensions() {
		HashMap<String, Integer> extAndNumber = new HashMap<>();
		
		for (TableRow row: table) {
			String fileExt = row.getFile().getFileExtension();
			Integer oldValue = extAndNumber.putIfAbsent(fileExt, 1); 
			if (oldValue != null) {
				extAndNumber.put(fileExt, oldValue.intValue() + 1);
			}
		}
		
		return extAndNumber;
	}
	
	/**
	 * Returns a map of all extensions with the lines of code per extension
	 * @return
	 */
	public HashMap<String, Integer> getExtensionsWithLOC() {
		HashMap<String, Integer> extAndNumber = new HashMap<>();
		
		for (TableRow row: table) {
			String fileExt = row.getFile().getFileExtension();
			int locHere = row.getLocInFile();
			Integer oldValue = extAndNumber.putIfAbsent(fileExt, locHere); 
			if (oldValue != null) {
				extAndNumber.put(fileExt, oldValue.intValue() + locHere);
			}
		}
		
		return extAndNumber;
	}
	
	/**
	 * Returns a HashMap of files with the lines of code per file
	 * @param extension to select the files
	 * @return
	 */
	public HashMap<IFile, Integer> getFilesWithLOCByExtension(String extension) {
		HashMap<IFile, Integer> filesWithLOC = new HashMap<>();
		for (TableRow row: table) {
			if (row.getFile().getFileExtension().equals(extension)) {
				filesWithLOC.put(row.getFile(), row.getLocInFile());
			}
		}
		return filesWithLOC;
	}
	
	/**
	 * Returns a HashMap of all FSTFeatures in this table with the number of appearance
	 * @return
	 */
	public HashMap<FSTFeature, Integer> getFeatures() {
		HashMap<FSTFeature, Integer> features = new HashMap<>();
		
		for (TableRow row: table) {
			for (FSTFeature singleFeature: row.getFeatures()) {
				Integer oldValue = features.putIfAbsent(singleFeature, 1);
				if (oldValue != null) {
					features.put(singleFeature, oldValue.intValue() +1);
				}
			}
		}
		
		return features;
	}
	
	/**
	 * Returns a HashMap of all FSTFeatures in this table with the lines of code per feature
	 * @return
	 */
	public HashMap<FSTFeature, Integer> getFeaturesWithLOC() {
		HashMap<FSTFeature, Integer> features = new HashMap<>();
		
		for (TableRow row: table) {
			for (FSTFeature singleFeature: row.getLocByFeatMap().keySet()) {
				int locInFeature = row.getLocByFeatMap().get(singleFeature);
				Integer oldValue = features.putIfAbsent(singleFeature, locInFeature);
				if (oldValue != null) {
					features.put(singleFeature, oldValue.intValue() +locInFeature);
				}
			}
		}
		
		return features;
	}
	
	/**
	 * Returns all files of this table
	 * @return
	 */
	public ArrayList<IFile> getFiles() {
		ArrayList<IFile> files = new ArrayList<>();
		
		for(TableRow row: table) {
			files.add(row.getFile());
		}
		
		return files;
	}
	
	/**
	 * Returns a HashMap of all features that are contained in files with the specified extension.
	 * The value for each entry in this map is the lines of code a given feature has.
	 * @param extension
	 * @return
	 */
	public HashMap<FSTFeature, Integer> getFeaturesByExtensionWithLOC(String extension) {
		HashMap<FSTFeature, Integer> features = new HashMap<>();
		
		for (TableRow row: table) {
			if (row.getFile().getFileExtension().equals(extension)) {
				
				for (FSTFeature feat: row.getFeatures()) {
					int featureLOC = row.getLocByFeatMap().get(feat);
					Integer oldValue = features.putIfAbsent(feat, featureLOC);
					if (oldValue != null) {
						features.put(feat, oldValue.intValue() + featureLOC);
					}
				}
			}
		}
		return features;
	}
	
	/**
	 * Returns a HashMap of all extensions and the lines of code within files with that
	 * extension, that contain the specified feature.
	 * @param feature to look for
	 * @return
	 */
	public HashMap<String, Integer> getExtensionsByFeatureWithLOC(FSTFeature feature) {
		HashMap<String, Integer> extensionsAndLOC = new HashMap<>();
		
		for (TableRow row: table) {
			String extension = row.getFile().getFileExtension();
			HashMap<FSTFeature, Integer> locByFeatMap = row.getLocByFeatMap();
			
			if (!locByFeatMap.isEmpty() && locByFeatMap.containsKey(feature)) {
				int locForFeature = row.getLocByFeatMap().get(feature);
				Integer oldValue = extensionsAndLOC.putIfAbsent(extension, locForFeature);
				if (oldValue != null) {
					extensionsAndLOC.put(extension, oldValue.intValue() + locForFeature);
				}
			}
			
		}
		
		return extensionsAndLOC;
	}
	
	/**
	 * Returns the feature by name
	 * @param featureName
	 * @return
	 */
	public FSTFeature resolveFeature(String featureName) {
		for (TableRow row: table) {
			if (!row.getLocByFeatMap().isEmpty()) {
				for (FSTFeature feat: row.getLocByFeatMap().keySet()) {
					if (feat.getName().equals(featureName)) {
						return feat;
					}
				}
			}
		}
		return null;
	}
	
	/**
	 * Returns an IFile by name
	 * @param fileName
	 * @return
	 */
	public IFile resolveFile(String fileName) { 
		for (TableRow row: table) {
			IFile file = row.getFile();
			if(file != null) {
				if(file.getName().equals(fileName)) {
					return file;
				}
			}
		}
		return null;
	}
	
	/**
	 * Returns a HashMap of all files that only contain a single feature.
	 * The HashMap contains the file as key and the feature as value.
	 * @return
	 */
	public HashMap<IFile, FSTFeature> getAllSingleFeatureFiles() {
		HashMap<IFile, FSTFeature> singleFeatFiles = new HashMap<>();
		for (TableRow row: table) {
			if (row.getFeatures().size() == 1) {
				singleFeatFiles.putIfAbsent(row.getFile(), row.getFeatures().get(0));
			}
		}
		
		return singleFeatFiles;
	}
	
	/**
	 * Returns the lines of code by extension
	 * @param extension to count loc for
	 * @return the lines of code
	 */
	public int getLOCByExtension(String extension) {
		int loc = 0;
		for (TableRow row: table) {
			if (row.getFile().getFileExtension().equals(extension)) {
				loc += row.getLocInFile();
			}
		}
		return loc;
	}
	
	/**
	 * Counts the lines of code in this mapper for a specific feature.
	 * @param feature to count the loc for
	 * @return the loc of feature
	 */
	public int getLOCByFeature(FSTFeature feature) {
		int loc = 0;
		for (TableRow row: table) {
			if (row.getLocByFeatMap().containsKey(feature)) {
				loc += row.getLocByFeatMap().get(feature).intValue();
			}
		}
		return loc;
	}
	
	/**
	 * Returns the lines of code of one file
	 * @param file
	 * @return the loc of file <br> 
	 * 		0 if file empty or not listed
	 */
	public int getLOCByFile(IFile file) {
		int loc = 0;
		for (TableRow row: table) {
			if (row.getFile().equals(file)) {
				loc += row.getLocInFile();
			}
		}
		return loc;
	}
	
	/**
	 * Returns all files that contain code of a feature
	 * @param feature to search for in files
	 * @return all files containing feature <br>
	 * 		null if feature isn't contained in any file
	 */
	public ArrayList<IFile> listAllFilesOfFeature(FSTFeature feature) {
		ArrayList<IFile> files = new ArrayList<>();
		for (TableRow row: table) {
			if (row.getFeatures().contains(feature)) {
				files.add(row.getFile());
			}
		}
		if (files.size() > 0) {
			return files;
		} else {
			return null;
		}
	}
	
	/**
	 * Returns the LOC per feature for one file
	 * @param file defines the file which is searched
	 * @return null or the HashMap containing the LOC per file
	 */
	public HashMap<FSTFeature, Integer> getLOCByFeatMap(IFile file) {
		TableRow row = searchRow(file);
		if(row != null) {
			return row.getLocByFeatMap();
		}
		return null;
	}
	
	/**
	 * Search a row in the table 
	 * @param file is used as an identifier
	 * @return null if the column wasn't found
	 */
	private TableRow searchRow(IFile file) {
		for (TableRow row: table) {
			if (row.getFile().equals(file)) {
				return row;
			}
		}
		return null;
	}
	
	public int locWithoutFeatures(IFile file) {
		TableRow row = searchRow(file);
		if(row != null) {
			HashMap<FSTFeature, Integer> featMap = row.getLocByFeatMap();
			if(featMap != null) {
				int featLOC = 0;
				for(FSTFeature feature: featMap.keySet()) {
					featLOC += featMap.get(feature).intValue();
					System.out.println("  LOC in feature "+ feature.getName() + ": " + featMap.get(feature).intValue());
				}
				System.out.println("All LOC in features: " + featLOC );
				System.out.println("LOCinFile: " + row.getLocInFile() );
				return row.getLocInFile() - featLOC;
			}
		}
		return 0;
	}
	
	/**
	 * Prints the table in an ugly way to the console
	 */
	public void printTableToConsole() {

		System.out.println("IFile       |  LOC  |  Map<Feat, LOC>");
		for (TableRow row: table) {
			System.out.print(row.getFile().getName() + "  |  ");
			System.out.print(row.getLocInFile() + "  |  ");
			for (FSTFeature feat: row.getLocByFeatMap().keySet()) {
				System.out.print("                    ");
				System.out.println(feat.getName() + ", " + row.getLocByFeatMap().get(feat));
			}
		}
	}
	
	/**
	 * 
	 * This inner class represents a table row as seen in the example of the parent class FileFeatureLOCMapper
	 * 
	 * @author Maximilian Homann
	 * @author Philipp Kuhn
	 */
	private class TableRow {
		//the columns
		private IFile file;
		private Integer locInFile;
		private HashMap<FSTFeature, Integer> locByFeatMap;
		
		/**
		 * constructor to create a complete column
		 * @param newFile
		 * @param newLocInFile
		 * @param newFeatureList
		 * @param newLocByFeat
		 */
		public TableRow(IFile newFile, int newLocInFile, HashMap<FSTFeature, Integer> newLocByFeat) {
			file = newFile;
			locInFile = newLocInFile;
			locByFeatMap = newLocByFeat;
		}

		/**
		 * constructor to create a column only filled with a file and lines of code
		 * @param newFile
		 * @param newLocInFile
		 */
		public TableRow(IFile newFile, int newLocInFile) {
			file = newFile;
			locInFile = newLocInFile;
			locByFeatMap = new HashMap<>();
		}
		
		/**
		 * Returns true of the feature is contained in this row
		 * @param feature
		 * @return
		 */
		public boolean containsFeature(FSTFeature feature) {
			return locByFeatMap.containsKey(feature);
		}
		
		/**
		 * Returns true of the feature is contained in this row
		 * @param feature
		 * @return
		 */
		public boolean containsFeature(String feature) {
			for (FSTFeature feat: locByFeatMap.keySet()) {
				if (feat.getName().equals(feature)) return true;
			}
			return false;
		}

		/* (non-Javadoc)
		 * @see java.lang.Object#equals(java.lang.Object)
		 */
		@Override
		public boolean equals(Object obj) {
			boolean equal = false;
			if (obj instanceof TableRow) {
				TableRow compareMe = (TableRow) obj;
				if (compareMe.getFile().equals(file)) {
					if (compareMe.getLocInFile() == locInFile) {
						if (compareMe.getLocByFeatMap().equals(locByFeatMap))
							return true;
						
					}
				}
			}
			return false;
		}

		/**
		 * @return the file
		 */
		public IFile getFile() {
			return file;
		}

		/**
		 * @param file the file to set
		 */
		public void setFile(IFile file) {
			this.file = file;
		}

		/**
		 * @return the locInFile
		 */
		public Integer getLocInFile() {
			return locInFile;
		}

		/**
		 * @param locInFile the locInFile to set
		 */
		public void setLocInFile(Integer locInFile) {
			this.locInFile = locInFile;
		}

		/**
		 * @return the featureList
		 */
		public List<FSTFeature> getFeatures() {
			ArrayList<FSTFeature> features = new ArrayList<>();
			for (FSTFeature feature: locByFeatMap.keySet()) {
				features.add(feature);
			}
			return features;
		}

		/**
		 * @return the locByFeat
		 */
		public HashMap<FSTFeature, Integer> getLocByFeatMap() {
			return locByFeatMap;
		}

		/**
		 * @param locByFeat the locByFeat to set
		 */
		public void setLocByFeatMap(HashMap<FSTFeature, Integer> locByFeat) {
			this.locByFeatMap = locByFeat;
		}
		
	}
}
