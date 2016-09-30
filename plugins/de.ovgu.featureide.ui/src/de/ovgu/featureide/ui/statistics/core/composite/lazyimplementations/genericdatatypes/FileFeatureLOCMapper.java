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
package de.ovgu.featureide.ui.statistics.core.composite.lazyimplementations.genericdatatypes;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

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
	public void addFullEntry(IFile file, int locInFile, List<FSTFeature> featureList, Map<FSTFeature, Integer> locByFeat) {
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
	public void addLocToEntry(IFile file, int LocInFile){
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
	 * Adds the featLocMap in the specified entry
	 * @param file specifies the entry
	 * @param locByFeat lines of code per feature in file
	 */
	public void addFeatLocMapToEntry(IFile file, Map<FSTFeature, Integer> locByFeat) {
		TableRow existingRow = searchRow(file);
		if(existingRow != null) {		
			if(existingRow.getLocByFeat() == null) {
				existingRow.setLocByFeat(locByFeat);
			}
			
		} else {
			listTable.add(new TableRow(file, locByFeat));
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
	 * 
	 * This inner class represents a table row as seen in the example of the parent class FileFeatureLOCMapper
	 * 
	 * @author Maximilian Homann
	 * @author Philipp Kuhn
	 */
	private class TableRow {
		//the columns
		public IFile file;
		public Integer locInFile;
		public List<FSTFeature> featureList;
		public Map<FSTFeature, Integer> locByFeat;
		
		/**
		 * constructor to create a complete column
		 * @param newFile
		 * @param newLocInFile
		 * @param newFeatureList
		 * @param newLocByFeat
		 */
		public TableRow(IFile newFile, int newLocInFile, List<FSTFeature> newFeatureList, Map<FSTFeature, Integer> newLocByFeat) {
			file = newFile;
			locInFile = newLocInFile;
			featureList = newFeatureList;
			locByFeat = newLocByFeat;
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
			locByFeat = newLocByFeat;;
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
							if (compareMe.getLocByFeat().equals(locByFeat))
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
		public Map<FSTFeature, Integer> getLocByFeat() {
			return locByFeat;
		}

		/**
		 * @param locByFeat the locByFeat to set
		 */
		public void setLocByFeat(Map<FSTFeature, Integer> locByFeat) {
			this.locByFeat = locByFeat;
		}
		
	}
}
