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

import java.io.File;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;

import featureide.core.CorePlugin;

/**
 * TODO description
 * 
 * @author Janet Feigenspan
 * @deprecated
 */
public class MemoryTestBench {
	
	private long memUsageBefore;
	private long memUsageAfter;
	private long memUsageDiff;
	
	public long getMemUsageBefore() {
		return memUsageBefore;
	}

	public void setMemUsageBefore(long memUsageBefore) {
		this.memUsageBefore = memUsageBefore;
	}

	public long getMemUsageAfter() {
		return memUsageAfter;
	}

	public void setMemUsageAfter(long memUsageAfter) {
		this.memUsageAfter = memUsageAfter;
	}

	public long getMemUsageDiff() {
		return memUsageDiff;
	}

	public void setMemUsageDiff(long memUsageDiff) {
		this.memUsageDiff = memUsageDiff;
	}

	public long memoryUsageWGarbageCol() {
	    garbageCollector(5);
	    long memUsage = Runtime.getRuntime().totalMemory() -
	      Runtime.getRuntime().freeMemory();
	    return memUsage;
	}
	  
	private void garbageCollector(int times) {
		for (int i = 0; i < times; i++) {
			System.gc();
		}		
	}

	public long memoryUsageWOGarbageCol() {
	    long memUsage = Runtime.getRuntime().totalMemory() -
	      Runtime.getRuntime().freeMemory();
	    return memUsage;
	}
	
	public void saveMemUsage() {

		File file = new File("C:\\MemUsage.txt");
	    try
	    {
	      new FileReader(file).read();
	    }
	    catch ( IOException e ) {
	    	CorePlugin.getDefault().logError(e);
	    }

		FileWriter fileWriter = null;
		try {
			fileWriter = new FileWriter(file, true);
			fileWriter.write(memUsageBefore + " " + memUsageAfter + " " + memUsageDiff + "\n");
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
		}
	}

}
