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
package de.ovgu.contracts.analysis;
import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.nio.charset.Charset;
import java.util.LinkedHashMap;
import java.util.Map;

/**
 * Runs JPF.
 * @author Jens Meinicke
 *
 */
// TODO customize jpf @ home\\.jpf
public class JavaPathfinder extends AbstractAnalyser {
	
    private static final int STATISTICS_OFFSET = 20;
    private static final Charset UTF_8 = Charset.availableCharsets().get("UTF-8");

	/**
	 * Runs JPF with following command:
	 * java -jar <jpf-core-dir>/build/RunJPF.jar +classpath=. <application-main-class>
	 */
	protected final Result run() {
		String[] commands = ("java "
				+ "-jar "
				+ JPF + "RunJPF.jar "
				+ "+classpath=" + BIN_PATH
				+ "," + JML
				+ MAIN_CLASS
				).split("[ ]");
		
		final ProcessBuilder processBuilder = new ProcessBuilder(commands);
		long time = System.currentTimeMillis();
		boolean foundError = false;
		Map<String, String> additions = new LinkedHashMap<>();
		try {
			Process process = processBuilder.start();
            
			final BufferedReader input = new BufferedReader(new InputStreamReader(
					process.getInputStream(), UTF_8));
			final BufferedReader error = new BufferedReader(new InputStreamReader(
					process.getErrorStream(), UTF_8));
			boolean x = true;
			
			while (x) {
					String line;
					while ((line = input.readLine()) != null) {
						System.out.println(line);
						if (line.contains("java.lang.AssertionError")) {
						    foundError = true;
						}
						if (line.startsWith("states:")) {
						    additions.put("states", line.substring(STATISTICS_OFFSET));
						} else if (line.startsWith("search:")) {
						    additions.put("search", line.substring(STATISTICS_OFFSET));
						} else if (line.startsWith("choice generators:")) {
						    additions.put("choice generators", line);
						} else if (line.startsWith("heap:")) {
						    additions.put("heap", line.substring(STATISTICS_OFFSET));
						} else if (line.startsWith("instructions:")) {
						    additions.put("instructions", line.substring(STATISTICS_OFFSET));
						} else if (line.startsWith("max memory:")) {
						    additions.put("max memory", line.substring(STATISTICS_OFFSET));
						} else if (line.startsWith("loaded code:")) {
						    additions.put("loaded code", line.substring(STATISTICS_OFFSET));
						}
					}
					while ((line = error.readLine()) != null) {
						System.out.println("JPF Error:" + line);
					}
					final int exitValue = process.exitValue();
					if (exitValue != 0) {
						System.err.println(exitValue);
					}
					x = false;
			}
			
		} catch (IOException e) {
            e.printStackTrace();
        }
		time = System.currentTimeMillis() - time;
		return new Result(getName(), time, foundError, additions);
	}

}
