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

import java.io.IOException;
import java.nio.file.DirectoryIteratorException;
import java.nio.file.DirectoryStream;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Queue;
import java.util.Set;
import java.util.stream.Collectors;

public class Scanner implements AutoCloseable {

    private final Path dir;
    private final String bundleRootFolder;
    private final Set<String> bundleBlackList = new HashSet<>();
    private final Set<String> fileExtensionsBlackList = new HashSet<>();
    private final Set<String> filePrefixesBlackList = new HashSet<>();
    private final String projectName;

    public Scanner(Path dir, String bundleFolder, String... skipBundles) {
        this.dir = dir;
        this.bundleRootFolder = bundleFolder;
        this.bundleBlackList.addAll(Arrays.asList(skipBundles));
        this.projectName = dir.toFile().getName();
    }

    public void skipFileTypes(String... fileExtensions) {
        fileExtensionsBlackList.addAll(Arrays.asList(fileExtensions));
    }

    public void skipFileNames(String... prefixes) {
        filePrefixesBlackList.addAll(Arrays.asList(prefixes));
    }

    Exporter exporter = new Exporter();

    public void doit() throws IOException {
        exporter.clear();

        System.out.println("┏━ Project: \"" + projectName + "\" (bundle root: \"" + bundleRootFolder + "\")");

        exporter.project(projectName);
        exporter.feature(projectName);

        for (String bundle : getBundleNames(dir, bundleRootFolder)) {
            bundle = bundle.substring(dir.toString().length() + bundleRootFolder.length() + 2);
            if (!bundleBlackList.contains(bundle)) {
                System.out.println("┃   ");
                System.out.println("┣━┳━ bundle " + bundle);

                final String bundleFeatureName = "bundle:" + bundle; 
                exporter.feature(bundleFeatureName);
                exporter.requires(bundleFeatureName, projectName);
                exporter.parent_of(projectName, "bundle:" + bundle);

                for (Path bundleFiles : scan(bundle)) {

                    //for (Path file : bundleFiles) {
                    //       System.out.println("file = " + file);
                    processFile(bundle, bundleFiles);
                    //}
                }
            } else {
                System.out.println("┃   ");
                System.out.println("┣━━ bundle: " + bundle + " (skipped)");
            }
        }
    }

    private Collection<String> getBundleNames(Path dir, String bundleFolder) {
        List<Path> result = new ArrayList<>();
        try (DirectoryStream<Path> stream = Files.newDirectoryStream(Paths.get(dir.toString() + "/" + bundleFolder))) {
            for (Path entry : stream) {
                if (entry.toFile().isDirectory()) {
                    result.add(entry);
                }
            }
        } catch (DirectoryIteratorException e) {
            e.printStackTrace();
        } catch (IOException e) {
            e.printStackTrace();
        }
        return result.stream().map((path) -> path.toString()).collect(Collectors.toList());
    }

    private void processFile(String bundleFolder, Path file) throws IOException {
        final String filePath = file.toString();

      //  System.out.println("Process file... " + filePath);
        String filename = Utils.getRelativeFilePath(filePath, dir, bundleRootFolder, bundleFolder);

        if (Utils.fileStartsWith(filePrefixesBlackList, filename)) {
            System.out.println("┃ ┃  ");
            System.out.println("┃ ┣━━ asset: " + filename + " (skipped)");
        } else {
            if (filePath.endsWith(".java")) {
                processJavaSourceFile(bundleFolder, filePath);
            } else if (filePath.endsWith("MANIFEST.MF")) {
                processManifestFile(bundleFolder, filePath);
            } else {
                processOtherFile(bundleFolder, filePath);
            }
        }
    }

    private void processManifestFile(String bundleFolder, String filePath) {
        System.out.println("┃ ┃  ");
        System.out.println("┃ ┣━┳━ manifest: " + Utils.getRelativeFilePath(filePath, dir, bundleRootFolder, bundleFolder));
        System.out.println("┃ ┃ ┣━┳━ requires ");
        for (String object : getExportedObjects(filePath))
            System.out.println("┃ ┃ ┃ ┣━━ " + object);

        final String manifestFeatureName = bundleFolder + "/" + Utils.getRelativeFilePath(filePath, dir, bundleRootFolder, bundleFolder);
        exporter.feature(manifestFeatureName);
        exporter.parent_of("bundle:" + bundleFolder, manifestFeatureName);
        exporter.requires(manifestFeatureName, "bundle:" + bundleFolder );

        for (String object : getExportedObjects(filePath)) {
            if (!object.trim().isEmpty()) {
            	final String requiredPackage = "package:" + object.trim();
            	exporter.requires(manifestFeatureName, requiredPackage);
            }
        }
    }

    private Collection<String> getExportedObjects(String filePath) {
        return new ManifestParser(filePath).getExportedObjects();
    }

    private void processOtherFile(String bundleFolder, String filePath) {
        String filename = filePath.substring(dir.toString().length() + 1 + bundleRootFolder.length() + 1 + bundleFolder.length() + 1);
        System.out.println("┃ ┃  ");
        System.out.println("┃ ┣━━ asset: " + filename + (fileExtensionsBlackList.contains(Utils.getFileExtension(filename))? " (skipped)" : ""));

        if (fileExtensionsBlackList.contains(Utils.getFileExtension(filename)))
            return;

        exporter.feature(bundleFolder + "/assets");
        exporter.feature(bundleFolder + "/" + filename);

        exporter.parent_of("bundle:" + bundleFolder, bundleFolder + "/assets");
        exporter.parent_of(bundleFolder + "/assets", bundleFolder + "/" + filename);

        exporter.requires("bundle:" + bundleFolder, bundleFolder + "/assets");
        exporter.requires(bundleFolder + "/assets", bundleFolder + "/" + filename);


//        exporter.parent_of(bundleFolder, manifestFeatureName);
//        exporter.requires(manifestFeatureName, bundleFolder);
    }

    private void processJavaSourceFile(String bundleFolder, String filePath) {
        // System.out.println(file);

        // final String className = getClassName(dir, filePath);
        // final String packageName = getPackageName(filePath);
        // final String resourceName = getResourceName(filePath);
        // final String bundleName = getBundleName(filePath);



        JavaSourceFileParser parser = new JavaSourceFileParser(filePath);

        final String bundleName = "bundle:" + bundleFolder;
        final String packageName = "package:" + parser.getPackage();
        final String className = "class:" + parser.getFullQualifiedClassName();
        String resourceName = filePath.substring(dir.toString().length() + 1 + bundleRootFolder.length() + 1 + bundleFolder.length() + 1);
        resourceName = resourceName.substring(0, resourceName.indexOf("/"));
        final Collection<JavaSourceFileParser.Import>  classImports = parser.getImports();

        System.out.println("┃ ┃  ");
        System.out.println("┃ ┣━┳━ class: " + className);
        System.out.println("┃ ┃ ┣━┳━ dependencies ");
        for (JavaSourceFileParser.Import imp : classImports)
            System.out.println("┃ ┃ ┃ ┣━━ " + imp.packageName+"."+imp.className);


        final String resourceNameFeature = bundleName + "/" + resourceName;
        
        exporter.feature(resourceNameFeature);
        exporter.feature(packageName);
        exporter.feature(className);
        exporter.feature(bundleName);
        
        if(bundleName.equals(packageName)) {
        	System.out.println("Blub");
        	System.exit(0);
        }

        exporter.parent_of(bundleName, resourceNameFeature);
        exporter.parent_of(resourceNameFeature, packageName);
        exporter.parent_of(packageName, className);


        for (JavaSourceFileParser.Import imp : classImports)
            exporter.requires(className, "class:" + imp.packageName+"."+imp.className);




    }

    private String getClassName(Path rootPath, String filePath) {
        return filePath.substring(rootPath.toString().length()).replace(".java", "");

    }

    private Collection<Path> scan(String bundleFolderName) throws IOException {
        List<Path> result = new ArrayList<>();
        Queue<Path> nextPathToExplore = new ArrayDeque<>();
        nextPathToExplore.add(Paths.get(dir.toString() + "/" + bundleRootFolder + "/" + bundleFolderName));

        while (!nextPathToExplore.isEmpty()) {
            Path actualDir = nextPathToExplore.poll();
         //   System.out.println("Scan bundle: " + actualDir);
            try (DirectoryStream<Path> stream = Files.newDirectoryStream(actualDir)) {
                for (Path entry : stream) {
                    if (entry.toFile().isDirectory()) {
                        nextPathToExplore.add(entry);
                    } else result.add(entry);
                }
            } catch (DirectoryIteratorException e) {
                throw e.getCause();
            }
        }
        return result;
    }

    @Override
    public void close() throws Exception {

    }


    public Exporter getExporter() {
        return exporter;
    }
}