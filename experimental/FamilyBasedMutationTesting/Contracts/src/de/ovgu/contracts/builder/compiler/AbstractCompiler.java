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
package de.ovgu.contracts.builder.compiler;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.nio.charset.Charset;
import java.util.List;

import de.ovgu.contracts.Defaults;

/**
 * Interface for compilers.
 * @author Jens Meinicke
 *
 */
public abstract class AbstractCompiler implements Defaults {
    
    private static final Charset UTF_8 = Charset.availableCharsets().get("UTF-8");

	public abstract void compile(String source, String destination);
	
	protected final void process(final List<String> command) {
        try {
            final ProcessBuilder processBuilder = new ProcessBuilder(command);
            final Process process = processBuilder.start();
            try (BufferedReader input = new BufferedReader(new InputStreamReader(
                    process.getInputStream(), UTF_8));
                    BufferedReader error = new BufferedReader(new InputStreamReader(
                    process.getErrorStream(), UTF_8));) {               
                boolean x = true;
                while (x) {
                    try {
                        String line;
                        while ((line = input.readLine()) != null) {
                            System.out.println(line);
                        }
                        while ((line = error.readLine()) != null) {
                            System.out.println("JavaC Error:" + line);
                        }
                        x = false;
                    } catch (IllegalThreadStateException e) {
                        e.printStackTrace();
                    }
                }
            } catch (IOException e) {
                e.printStackTrace();
            }
        } catch (IOException e) {
            e.printStackTrace();
        }
    }
}
