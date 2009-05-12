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
package featureide.core.performanceTest;

/**
 * TODO #29: Documentation: What is the purpose of this class?
 * 
 * @author Janet Feigenspan
 * @deprecated
 */
public class ExecutionTimeTestBench {
	
	private long start;
	private long end;
	private long diff;
	public void setEnd(long end) {
		this.end = end;
	}
	public long getEnd() {
		return end;
	}
	public void setStart(long start) {
		this.start = start;
	}
	public long getStart() {
		return start;
	}
	public void setDiff(long diff) {
		this.diff = diff;
	}
	public long getDiff() {
		return diff;
	}

	public void saveExecTime() {
		
		/*File file = new File("C:\\ExecTime.txt");
	    try
	    {
	      new FileReader(file).read();
	    }
	    catch ( IOException e ) {
	      System.out.println("Fehler beim Lesen der Datei");
	    }

		FileWriter fileWriter = null;
		try {
			fileWriter = new FileWriter(file, true);
			fileWriter.write(start + " " + end + " " + diff + "\n");
			fileWriter.flush();
			
		} catch (IOException e) {
			e.printStackTrace();
		}
		
		// close the fileWriter
		finally { 
		  if ( fileWriter != null ) 
		    try { fileWriter.close();
		    } catch (IOException e) {
		    	e.printStackTrace();
		    } 
		}*/
	}
}
