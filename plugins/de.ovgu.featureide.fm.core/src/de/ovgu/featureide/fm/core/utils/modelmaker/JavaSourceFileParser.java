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
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;

public class JavaSourceFileParser {

    private final String filename;
    private String packageName;
    private String className;
    private String fullQualifiedClassName;
    private Collection<JavaSourceFileParser.Import> imports = new ArrayList<>();


    public JavaSourceFileParser(String filename) {
        this.filename = filename;
        parse();
    }

    private void parse() {
        StringBuilder classNameBuilder = new StringBuilder(filename.replace(".java", "")).reverse();
        className = new StringBuilder(classNameBuilder.substring(0, classNameBuilder.indexOf("/"))).reverse().toString();


        try (BufferedReader br = new BufferedReader(new FileReader(new File(filename)))) {
            String line;
            while ((line = br.readLine()) != null) {
                if (line.contains("package")) {
                    packageName = line.trim().substring("package".length()).replace(";", "").trim();
                } else if (line.contains("import")) {
                    if (line.trim().startsWith("*") || line.trim().startsWith("/")) {
                        continue;
                    }

                    String importDefinition = line.trim().substring("import".length() + 1).replace(";","").trim();

                   String importedPackage, importedClassName;

                    if (importDefinition.startsWith("static")) {
                        importDefinition = importDefinition.substring("static".length()).trim();
                        importedClassName = Utils.getCurrentPackageIdentifier(Utils.goPackageLevelUp(importDefinition));
                        importedPackage = Utils.goPackageLevelUp(Utils.goPackageLevelUp(importDefinition));
                    } else {
                        importedClassName = Utils.getCurrentPackageIdentifier(importDefinition);
                        importedPackage = Utils.goPackageLevelUp(importDefinition);
                    }

                    imports.add(new Import(importedPackage, importedClassName));

                } else if (line.contains("{"))
                    break;
            }
        } catch (FileNotFoundException e) {
            e.printStackTrace();
        } catch (IOException e) {
            e.printStackTrace();
        }
    }

    public String getPackage() {
        return  packageName;
    }

    public String getClassName() {
        return className;
    }

    public String getFullQualifiedClassName() {
        return packageName + "." + className;
    }

    public Collection<JavaSourceFileParser.Import> getImports() {
        return Collections.unmodifiableCollection(imports);
    }

    public static class Import {
        String packageName;
        String className;

        public Import(String packageName, String className) {
            this.packageName = packageName;
            this.className = className;
        }

    }
}
