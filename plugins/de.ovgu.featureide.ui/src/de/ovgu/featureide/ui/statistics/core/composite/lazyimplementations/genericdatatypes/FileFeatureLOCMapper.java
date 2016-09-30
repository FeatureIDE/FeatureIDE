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
package de.ovgu.featureide.ui.statistics.core.composite.lazyimplementations.genericdatatypes;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.HashMap;

import org.eclipse.core.resources.IFile;

import de.ovgu.featureide.core.fstmodel.FSTFeature;

/**
 * A class to represent the following table of information: <br>
 * <table>
  <tr>
    <th>IFile | </th>
    <th>loc by file | <br></th>
    <th>List&lt;FSTFeature&gt; | </th>
    <th>Map&lt;FSTFeature, loc by feature&gt;<br></th>
  </tr>
  <tr>
  	<th>Hello.java
  	<th>201
  	<th>feat1, feat2
  	<th>(feat1,101),(feat2,100)
  </tr>
  </table>
 * 
 * @author Maximilian Homann
 * @author Philipp Kuhn
 */
public class FileFeatureLOCMapper {

	private ArrayList<TableRow> listTable = new ArrayList<TableRow>();
	/**
	 * Adds a complete entry
	 * @param file the file works as an unique Identifier for each row
	 * @param locInFile the lines of code in file
	 * @param featureList A list of features used in file
	 * @param locByFeat lines of code per feature in file
	 */
	public void addEntry(IFile file, int locInFile, ArrayList<FSTFeature> featureList, HashMap<FSTFeature, Integer> locByFeat) {
		TableRow newRow = new TableRow(file, locInFile, featureList, locByFeat);
		if (!listTable.contains(newRow)) {
			listTable.add(newRow);
		}
	}
	/**
	 * Adds 'lines of code' in the specified entry
	 * (only if there wasn't any)
	 * @param file specifies the entry
	 * @param LocInFile the lines of code in file
	 */
	public void addLOCToEntry(IFile file, int LocInFile){
		TableRow existingRow = searchRow(file);
		if(existingRow != null) {
			if(existingRow.getLocInFile() == null) {
				existingRow.setLocInFile(LocInFile);
			}
		} else {
			listTable.add(new TableRow(file, LocInFile));
		}	
	}
	/**
	 * Adds the featureList in the specified entry
	 * @param file specifies the entry
	 * @param featureList A list of features used in file
	 */
	public void addFeatListToEntry(IFile file, List<FSTFeature> featureList){
		TableRow existingRow = searchRow(file);
		if(existingRow != null) {		
			if(existingRow.getFeatureList() == null) {
				existingRow.setFeatureList(featureList);
			}	
		} else {
			listTable.add(new TableRow(file, featureList));
		}	
	}
	
	/**
	 * Add a single feature to the list of features for file
	 * @param file the file for the new feature
	 * @param feat the new feature
	 */
	public void addSingleFeatToEntry(IFile file, FSTFeature feat) {
		TableRow existingRow = searchRow(file);
		if (existingRow != null) {
			if (existingRow.getFeatureList() == null) {
				existingRow.setFeatureList(new ArrayList<FSTFeature>());
			}
			if (!existingRow.getFeatureList().contains(feat)) {
				existingRow.getFeatureList().add(feat);
			}
		}
	}
	
	/**
	 * Adds a feature LOC map to the entry specified by file
	 * @param file specifies the entry
	 * @param locByFeat lines of code per feature in file
	 */
	public void addFeatLOCMapToEntry(IFile file, Map<FSTFeature, Integer> locByFeat) {
		TableRow existingRow = searchRow(file);
		if(existingRow != null) {		
			if(existingRow.getLocByFeatMap() == null) {
				existingRow.setLocByFeatMap(locByFeat);
			}
			
		} else {
			listTable.add(new TableRow(file, locByFeat));
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
	 * searching a row in the column 
	 * @param file is used as an identifier
	 * @return null if the column wasn't found
	 */
	private TableRow searchRow(IFile file) {
		TableRow existingRow = null;
		for(int i = 0; i < listTable.size(); i++) {
			TableRow row = listTable.get(i);
			if (row.getFile().equals(file)) {
				existingRow = listTable.get(i);
				break;
			}
		}
		return existingRow;
	}
	
	/**
	 * Prints the table in an ugly way to the console
	 */
	public void printTableToConsole() {
		System.out.println("IFile  |  LOC  |  ListOfFeat  |  Map<Feat, LOC>");
		for (TableRow row: listTable) {
			System.out.print(row.getFile().getName() + "  |  ");
			System.out.print(row.getLocInFile() + "  |  ");
			for (FSTFeature feat: row.getFeatureList()) {
				System.out.println(feat.getName());
			}
			System.out.print("  |  ");
			for (FSTFeature feat: row.getLocByFeatMap().keySet()) {
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
		private List<FSTFeature> featureList;
		private Map<FSTFeature, Integer> locByFeatMap;
		
		/**
		 * constructor to create a complete column
		 * @param newFile
		 * @param newLocInFile
		 * @param newFeatureList
		 * @param newLocByFeat
		 */
		public TableRow(IFile newFile, int newLocInFile, ArrayList<FSTFeature> newFeatureList, HashMap<FSTFeature, Integer> newLocByFeat) {
			file = newFile;
			locInFile = newLocInFile;
			featureList = newFeatureList;
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
		}

		/**
		 * constructor to create a column only filled with a file and a featureList
		 * @param newFile
		 * @param newFeatureList
		 */
		public TableRow(IFile newFile, List<FSTFeature> newFeatureList) {
			file = newFile;
			featureList = newFeatureList;
		}

		/**
		 * constructor to create a column only filled with a file and lines of code per feature
		 * @param newFile
		 * @param newLocByFeat
		 */
		public TableRow(IFile newFile, Map<FSTFeature, Integer> newLocByFeat) {
			file = newFile;
			locByFeatMap = newLocByFeat;;
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
						if (compareMe.getFeatureList().equals(featureList)) {
							if (compareMe.getLocByFeatMap().equals(locByFeatMap))
								return true;
						}
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
		public List<FSTFeature> getFeatureList() {
			return featureList;
		}

		/**
		 * @param featureList the featureList to set
		 */
		public void setFeatureList(List<FSTFeature> featureList) {
			this.featureList = featureList;
		}

		/**
		 * @return the locByFeat
		 */
		public Map<FSTFeature, Integer> getLocByFeatMap() {
			return locByFeatMap;
		}

		/**
		 * @param locByFeat the locByFeat to set
		 */
		public void setLocByFeatMap(Map<FSTFeature, Integer> locByFeat) {
			this.locByFeatMap = locByFeat;
		}
		
	}
}
