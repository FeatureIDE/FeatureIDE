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
package de.ovgu.contracts.utils;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.IOException;
import java.nio.channels.FileChannel;
import java.util.LinkedList;
import java.util.List;

import javax.annotation.Nonnull;

/**
 * Manages default file operations.
 * @author Jens Meinicke
 *
 */
public final class FileManager {
    
    private FileManager() { }

    /**
     * Removes the resource.
     * @param source The file or folder to remove
     */
    public static void removeFiles(@Nonnull final String path) {
        FileManager.removeFiles(new File(path));
    }
    
    /**
     * Removes the resource.
     * @param source The file or folder to remove
     */
	public static void removeFiles(@Nonnull final File source) {
	    if (source == null || !source.exists()) {
	        return;
	    }
		for (final File file : source.listFiles()) {
			if (file.isDirectory()) {
				removeFiles(file);
			} else {
				file.delete();
			}
		}
        source.delete();
	}
	
    /**
     * Copies the resource.
     * @param source The file or folder to copy
     * @param destination The destination of the copy operation
     */
	public static void copyFiles(final File source, final String destination) {
		for (final File file : source.listFiles()) {
			if (file.isDirectory()) {
				copyFiles(file, destination + file.getName() + "\\");
				final File folder  = new File(destination + file.getName());
				if (!folder.exists()) {
					folder.mkdirs();
				}
			} else {
				if (file.getName().endsWith(".java")) {
					copyFile(file, new File(destination + file.getName()));
				}
			}
		}
		
	}
	
	private static void copyFile(final File source, final File destination) {
	    if (!destination.exists()) {
            try {
                createFolder(destination.getParentFile());
                destination.createNewFile();
            } catch (IOException e) {
                e.printStackTrace();
            }
        }
	    try (FileChannel src = new FileInputStream(source).getChannel();
		     FileChannel dest = new FileOutputStream(destination).getChannel()) {
			
			dest.transferFrom(src, 0, src.size());
		} catch (IOException e) {
		    e.printStackTrace();
		}
	}
	
   
	
	/**
	 * Creates the file and all necessary directories.
	 * @param file The file to create
	 */
	static void createFile(final File file) {
		if (!file.exists()) {
			createFolder(file.getParentFile());
			try {
				file.createNewFile();
			} catch (IOException e) {
				e.printStackTrace();
			}			
		}
	}
	
	   /**
     * Creates the file and all necessary directories.
     * @param file The file to create
     */
    public static void createFolder(final String path) {
        createFolder(new File(path));
    }
    
    /**
     * Creates the file and all necessary directories.
     * @param file The file to create
     */
    private static void createFolder(final File folder) {
        if (!folder.exists()) {
            folder.mkdirs();
        }
    }
    
    public static List<File> listFiles(final File directory, final String[] extensions, 
            final boolean subDerectories) {
        return listFiles(directory, extensions, subDerectories, new LinkedList<File>());
    }
    

    private static List<File> listFiles(final File directory, final String[] extensions, 
            final boolean subDerectories, final List<File> files) {
        for (final File child : directory.listFiles()) {
            if (child.isFile()) {
                for (String extension : extensions) {
                    if (child.getName().endsWith(extension)) {
                        files.add(child);
                    }
                }
            } else if (subDerectories && child.isDirectory()) {
                listFiles(child, extensions, subDerectories, files);
            }
        }
        return files;
    }
    
    public static List<File> listAll(final File directory, final boolean subDerectories) {
        return listAll(directory, subDerectories, new LinkedList<File>());
    }
    
    private static List<File> listAll(final File directory, final boolean subDerectories, final List<File> files) {
        for (final File child : directory.listFiles()) {
            files.add(child);
            if (subDerectories && child.isDirectory()) {
                listAll(child, subDerectories, files);
            }
        }
        return files;
    }
}
