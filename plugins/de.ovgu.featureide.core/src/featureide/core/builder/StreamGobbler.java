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
package featureide.core.builder;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.util.ArrayList;

import featureide.core.CorePlugin;

/**
 * Gets the output from an external programm (e.g. Cygwin)
 * 
 * @author Janet Feigenspan
 * @deprecated
 */
public class StreamGobbler extends Thread
{
    InputStream input;
    String type;
    ArrayList<String> errors = new ArrayList<String>();
    
    StreamGobbler(InputStream input, String type)
    {
        this.input = input;
        this.type = type;
    }
    
    public void run()
    {
    	try
    	{
    		InputStreamReader inputReader = new InputStreamReader(input);
    		BufferedReader br = new BufferedReader(inputReader);
    		String line = null;
    		while ( (line = br.readLine()) != null) {
    			CorePlugin.getDefault().logInfo(type + ">" + line);
    			errors.add(line);
    		}
    	} catch (IOException ioe)
    	{
    		ioe.printStackTrace();  
    	}
    }
}
