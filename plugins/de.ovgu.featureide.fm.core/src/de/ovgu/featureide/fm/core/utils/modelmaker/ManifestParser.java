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
package de.ovgu.featureide.fm.core.utils.modelmaker;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.util.Collection;
import java.util.HashSet;


public class ManifestParser {

    String filePath;
    private Collection<String> exportedObjects = new HashSet<>();

    public ManifestParser(String filePath) {
        this.filePath = filePath;
        readExportedObjects();
    }

    private void readExportedObjects() {

        try (BufferedReader br = new BufferedReader(new FileReader(new File(filePath)))) {
            String line;
            boolean exportedPackageChunk = false;
            while ((line = br.readLine()) != null) {
                exportedPackageChunk |= line.contains("Export-Package:");
                if (exportedPackageChunk) {
                    line = line.replace("Export-Package:", "").trim();
                    line = line.replace("uses:=", "").trim();
                    line = line.replace(";", ",").trim();
                    line = line.replace("\"", "").trim();

                    if (line.contains(":"))
                        break;

                    String[] exports = line.contains(",")? line.split(",") : new String[] { line };

                    for (String export : exports)
                        exportedObjects.add(export.trim());



                }
            }
        } catch (FileNotFoundException e) {
            e.printStackTrace();
        } catch (IOException e) {
            e.printStackTrace();
        }

    }


    public Collection<String> getExportedObjects() {
        return exportedObjects;
    }
}