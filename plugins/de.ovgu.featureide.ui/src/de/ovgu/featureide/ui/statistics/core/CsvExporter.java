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
package de.ovgu.featureide.ui.statistics.core;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.IJobChangeEvent;
import org.eclipse.core.runtime.jobs.IJobChangeListener;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.FileDialog;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.progress.UIJob;

import de.ovgu.featureide.fm.ui.editors.featuremodel.GUIDefaults;
import de.ovgu.featureide.ui.UIPlugin;
import de.ovgu.featureide.ui.statistics.core.composite.Parent;

/**
 * Handles the export of information from {@link TreeViewer}. Consists of a
 * {@link FileDialog} following by an export to a *.csv-file. If the export
 * fails the user gets the chance to repeat it, so his selection isn't lost.
 * 
 * @author Dominik Hamann
 * @author Patrick Haese
 */
public class CsvExporter {
	private Shell shell;
	public static final String SEPARATOR = ";";

	public CsvExporter(Shell shell) {
		super();
		this.shell = shell;
	}
	
	private String returnVal;
	
	private Object[] visibleExpandedElements;
	
	public void export(final Object[] export) {
		
		UIJob uiJob = new UIJob("") {
			@Override
			public IStatus runInUIThread(IProgressMonitor monitor) {
				visibleExpandedElements = export;				
				FileDialog dialog = new FileDialog(shell);
				dialog.setFilterExtensions(new String[] { "*.csv" });
				dialog.setText("choose wisely");
				returnVal = dialog.open();
				if (returnVal == null) {
					return Status.CANCEL_STATUS;
				}
				return Status.OK_STATUS;
			}
		};
		
		uiJob.setPriority(Job.INTERACTIVE);
		uiJob.schedule();
		uiJob.addJobChangeListener(new IJobChangeListener() {
			
			@Override
			public void sleeping(IJobChangeEvent event) {}
			
			@Override
			public void scheduled(IJobChangeEvent event) {}
			
			@Override
			public void running(IJobChangeEvent event) {}
			
			@Override
			public void done(IJobChangeEvent event) {
				if (event.getResult() == Status.OK_STATUS) {
					actualExport();
				}
			}
			
			@Override
			public void awake(IJobChangeEvent event) {}
			
			@Override
			public void aboutToRun(IJobChangeEvent event) {}
		});
		
	}
	
	/**
	 * Puts the description of each selected node in the first row as header and
	 * it's value in the second row.
	 * 
	 */
	private void actualExport() {
		Job job = new Job("Export statistics into csv") {
			
			private StringBuilder firstBuffer;
			private StringBuilder secondBuffer;
			
			@Override
			protected IStatus run(IProgressMonitor monitor) {
				
				List<String> descs = new LinkedList<String>();
				List<String> vals = new LinkedList<String>();
				getExportData(descs, vals);
				firstBuffer = new StringBuilder();
				secondBuffer = new StringBuilder();
				prepareDataForExport(descs, vals, firstBuffer, secondBuffer);
				return actualWriting();
			}
			
			/**
			 * @param firstBuffer
			 * @param secondBuffer
			 * @return
			 */
			private IStatus actualWriting() {
				BufferedWriter writer = null;
				
				if (!returnVal.endsWith(".csv")) {
					returnVal += ".csv";
				}
				File file = new File(returnVal);
				try {
					if (!file.exists()) {
						file.createNewFile();
					}
					writer = new BufferedWriter(new OutputStreamWriter(new FileOutputStream(file)));
					writer.write(firstBuffer.toString());
					writer.newLine();
					writer.write(secondBuffer.toString());
				} catch (FileNotFoundException e) {
					giveUserFeedback(true);
					return Status.CANCEL_STATUS;
				} catch (IOException e) {
					UIPlugin.getDefault().logError(e);
				} finally {
					if (writer != null) {
						try {
							writer.close();
						} catch (IOException e) {
							UIPlugin.getDefault().logError(e);
						}
					}
				}
				giveUserFeedback(false);
				return Status.OK_STATUS;
			}
			
			/**
			 * 
			 */
			private void giveUserFeedback(final boolean error) {
				UIJob errorJob = new UIJob(error ? "show errordialog" : "show dialog") {
					
					@Override
					public IStatus runInUIThread(IProgressMonitor monitor) {
						Shell shell = Display.getDefault().getActiveShell();
						if (error) {
							MessageDialog dial = new MessageDialog(shell, "Error", GUIDefaults.FEATURE_SYMBOL, "The file cannot be accessed!\nTry again?",
									MessageDialog.ERROR, new String[] { "OK", "Cancel" }, 0);
							if (dial.open() == 0) {
								actualWriting();
							}
						} else {
							// MessageDialog.openInformation(shell, ,
							// "Data was successfully exported.");
							new MessageDialog(shell, "Success", GUIDefaults.FEATURE_SYMBOL, "Data was successfully exported", MessageDialog.INFORMATION,
									new String[] { "OK" }, 0).open();
						}
						
						return Status.OK_STATUS;
					}
				};
				errorJob.setPriority(INTERACTIVE);
				errorJob.schedule();
			}
			
			/**
			 * @param descs
			 * @param vals
			 * @param buffer
			 * @param secBuf
			 */
			private void prepareDataForExport(List<String> descs, List<String> vals, StringBuilder buffer, StringBuilder secBuf) {
				for (String desc : descs) {
					buffer.append(desc);
					buffer.append(SEPARATOR);
				}
				for (String val : vals) {
					secBuf.append(val);
					secBuf.append(SEPARATOR);
				}
			}
			
			/**
			 * @param descs
			 * @param vals
			 */
			private void getExportData(List<String> descs, List<String> vals) {
				descs.add("Description: ");
				vals.add("Value: ");
				Parent last = null;
				for (Object o : visibleExpandedElements) {
					if (o instanceof Parent) {
						Parent parent = ((Parent) o);
						if (parent.getParent().equals(last)) {
							int end = descs.size() - 1;
							descs.set(end, descs.get(end) + ":");
						}
						descs.add(parent.getDescription());
						vals.add(parent.getValue() != null ? parent.getValue().toString() : "");
						last = parent;
					}
				}
			}
		};
		job.setPriority(Job.SHORT);
		job.schedule();
	}
}
