/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2013  FeatureIDE team, University of Magdeburg, Germany
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
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.fm.core.editing.evaluation;

import java.io.File;
import java.io.PrintWriter;
import java.util.Date;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;
import org.sat4j.specs.TimeoutException;

import de.ovgu.featureide.fm.core.FMCorePlugin;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.editing.Comparison;
import de.ovgu.featureide.fm.core.editing.ModelComparator;
import de.ovgu.featureide.fm.core.io.FeatureModelReaderIFileWrapper;
import de.ovgu.featureide.fm.core.io.FeatureModelWriterIFileWrapper;
import de.ovgu.featureide.fm.core.io.xml.XmlFeatureModelReader;
import de.ovgu.featureide.fm.core.io.xml.XmlFeatureModelWriter;

/**
 * A class to evaluate the performance of the comparison of feature models.
 * 
 * @author Thomas Thuem
 */
public class Evaluation {
	
//	final static int[] sizes = new int[] {10, 20, 50, 100, 200, 500, 1000, 2000, 5000, 10000};
//	final static int[] edites = new int[] {10};
//	final static int[] edites2 = new int[] {0, 1, 2, 5, 10, 20, 30, 40, 50, 60, 70, 80, 90, 100};
//	final static int[] sizes = new int[] {1000};
//	final static int[] edites = new int[] {10};
//	final static int[] edites2 = new int[] {10};
	final static int[] sizes = new int[] {2, 4, 6, 8, 10, 12, 14, 16, 18, 20};
	final static int[] edites = new int[] {3};
	final static int[] edites2 = new int[] {3};

//	static int id = 500;
//	static int count = 100;

	public static void evaluate(IProject project) {
		FMCorePlugin.getDefault().logInfo("Evaluation.evaluate(" + project + ")");
		try {
			long start = System.nanoTime();
//			File outFile = new File(project.getLocation().toOSString() + "\\generation " + id + " " + new Date().toString().replace(':', '.') + ".txt");
//			File outFile = new File(project.getLocation().toOSString() + "\\newcalculation 0-39 " + new Date().toString().replace(':', '.') + ".txt");
//			File outFile = new File(project.getLocation().toOSString() + "\\valid 0-39 " + new Date().toString().replace(':', '.') + ".txt");
			File outFile = new File(project.getLocation().toOSString() + "\\comparison " + new Date().toString().replace(':', '.') + ".txt");
			PrintWriter out = new PrintWriter(outFile);
			System.out.println("########## Evaluation Begin");
			out.flush();
			
//			generateModels(project, out, id, id + count - 1);

//			calculationTime(project, out);

//			out.println("features	fmid	valid");
//			for (int i = 1; i <= 5; i++)
//				checkModels(project, out, i*100, i*100+39);
			
			long dur = System.nanoTime() - start;
			System.out.println("########## Evaluation End (" + Generator.getTimeString(dur) + ")");
			out.close();
		} catch (Exception e) {
			FMCorePlugin.getDefault().logError(e);
		}
	}

	static void calculationTime(IProject project, PrintWriter out) {
		out.println("features	edits	kind	output	fmid	editid	strat0	strat1	strat2	strat3");
		ModelComparator[] comparator = new ModelComparator[4];
		for (int i = 0; i < comparator.length; i++)
			comparator[i] = new ModelComparator(60000, i);
		//IFeatureModelReader reader = new XmlFeatureModelReader(null,project);
		FeatureModelReaderIFileWrapper reader = new FeatureModelReaderIFileWrapper(new XmlFeatureModelReader(null));
		//IFeatureModelWriter writer = new XmlFeatureModelWriter(null);
		FeatureModelWriterIFileWrapper writer = new FeatureModelWriterIFileWrapper(new XmlFeatureModelWriter(null));
		for (int k = 0; k < sizes.length; k++)
			for (int i = 1; i <= 5; i++) {
				int start = i*100;
				int end = i*100 + 39;
				for (int id = start; id <= end; id++) {
					
					//20-210, 18-400, 20-428
					if (sizes[k] < 20) continue;
					if (sizes[k] == 20 && id <= 429) continue;
					
					try {
						//open or generate feature model
						int size = sizes[k];
						IFolder folder = project.getFolder(size + "");
						IFile file = folder.getFile(size + "-" + id + ".m");
						System.out.println(file);
						FeatureModel fm1;
						if (file.exists()) {
							fm1 = new FeatureModel();
							reader.setFeatureModel(fm1);
							reader.readFromFile(file);
						}
						else {
							if (!folder.exists())
								folder.create(false, false, null);
							fm1 = Generator.generateFeatureModel(id, size);
							writer.setFeatureModel(fm1);
							writer.writeToFile(file);
						}

						int[] edites = size != 1000 ? Evaluation.edites : Evaluation.edites2;
						for (int l = 0; l < edites.length; l++) {
							int edits = edites[l];
							int seed = id*10;
							
							Comparison[] editName = new Comparison[] {Comparison.REFACTORING, Comparison.GENERALIZATION, Comparison.ARBITRARY};
							for (int m = 2; m < 3; m++) {
								try {
									IFolder subfolder = folder.getFolder(editName[m].name());
									if (!subfolder.exists())
										subfolder.create(true, false, null);
									IFile file2 = subfolder.getFile(size + "-" + id + "-" + edits + "-" + (seed+m) + ".m");
									System.out.println("\t" + file2);

									FeatureModel fm2;
									if (file2.exists()) {
										fm2 = new FeatureModel();
										reader.setFeatureModel(fm2);
										reader.readFromFile(file2);
									}
									else {
										//apply refactoring/generalization/arbitrary edit
										if (m == 0)
											fm2 = Generator.refactoring(fm1, seed+m, edits);
										else if (m == 1)
											fm2 = Generator.generalization(fm1, seed+m, edits);
										else
											fm2 = Generator.arbitraryEdits(fm1, seed+m, edits);
										//save edited feature model
										writer.setFeatureModel(fm2);
										writer.writeToFile(file2);
									}
									
									//measure calculation time
									Comparison c = null;
									long[] time = new long[comparator.length];
									for (int n = 0; n < time.length; n++) {
										time[n] = System.nanoTime();
										c = comparator[n].compare(fm1, fm2);
										time[n] = System.nanoTime() - time[n];
										System.out.println(time[n]/1000000);
									}

									//print data
									out.print(size + "\t");
									out.print(edits + "\t");
									out.print(editName[m] + "\t");
									out.print(c + "\t");
									out.print(id + "\t");
									out.print((seed+m) + "\t");
									for (int n = 0; n < time.length; n++)
										out.print(time[n] + "\t");
									out.println();
									out.flush();
								} catch (Exception e) {
									FMCorePlugin.getDefault().logError(e);
								}
							}
						}
					} catch (Exception e) {
						FMCorePlugin.getDefault().logError(e);
					}
				}
			}
	}
	
	static void generateModels(IProject project, PrintWriter out, int start, int end) {
			for (int id = start; id <= end; id++)
				for (int i = 0; i < sizes.length; i++){
					int size = sizes[i];
					IFolder folder = project.getFolder(size + "");
					IFile file = folder.getFile(size + "-" + id + ".m");
					if (file.exists()) {
						System.out.println(file + " skipped");
						continue;
					}
					
					FeatureModel fm = Generator.generateFeatureModel(id, size);
					//IFeatureModelWriter writer = new XmlFeatureModelWriter(fm);
					FeatureModelWriterIFileWrapper writer = new FeatureModelWriterIFileWrapper(new XmlFeatureModelWriter(fm));
					boolean valid = false;
					try {
						if (!folder.exists())
							folder.create(false, false, null);
						writer.writeToFile(file);
						
						FeatureModel fmout = new FeatureModel();
						//IFeatureModelReader reader = new XmlFeatureModelReader(fmout,project);
						FeatureModelReaderIFileWrapper reader = new FeatureModelReaderIFileWrapper(new XmlFeatureModelReader(fmout));
						reader.readFromFile(file);
						valid = fmout.getAnalyser().isValid();
					} catch (Exception e) {
						FMCorePlugin.getDefault().logError(e);
					}
					if (!valid) {
						out.println(file + " deleted");
						out.flush();
						try {
							file.delete(false, null);
						} catch (CoreException ce) {
						}
					}
				}
		}

	static void checkModels(IProject project, PrintWriter out, int start, int end) {
		for (int id = start; id <= end; id++)
			for (int k = 0; k < sizes.length; k++) {
				int size = sizes[k];
				boolean valid = false;
				do {
					//open feature model
					IFolder folder = project.getFolder(size + "");
					IFile file = folder.getFile(size + "-" + id + ".m");
					FeatureModel fm = new FeatureModel();
					//IFeatureModelReader reader = new XmlFeatureModelReader(fm,project);
					FeatureModelReaderIFileWrapper reader = new FeatureModelReaderIFileWrapper(new XmlFeatureModelReader(fm));
					//check if it is valid
					String output = null;
					try {
						reader.readFromFile(file);
						valid = fm.getAnalyser().isValid();
						output = "" + valid;
					} catch (Exception e) {
						FMCorePlugin.getDefault().logError(e);
						output = e.toString();
					}
					output = size + "\t" + id + "\t" + output;
					out.println(output);
					out.flush();
					System.out.println(output);
					System.out.flush();
					if (!valid) {
						//generate a new one
						fm = Generator.generateFeatureModel(id, size);
						try {
							System.out.println(fm.getAnalyser().isValid());
						} catch (TimeoutException e) {
							FMCorePlugin.getDefault().logError(e);
						}
						//IFeatureModelWriter writer = new XmlFeatureModelWriter(fm);
						FeatureModelWriterIFileWrapper writer = new FeatureModelWriterIFileWrapper(new XmlFeatureModelWriter(fm));
						try {
							writer.writeToFile(file);
						} catch (CoreException e) {
							FMCorePlugin.getDefault().logError(e);
						}
					}
				} while (!valid);
			}
	}

}
