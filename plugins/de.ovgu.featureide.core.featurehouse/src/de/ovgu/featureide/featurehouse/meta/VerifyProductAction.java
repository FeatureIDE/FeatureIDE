package de.ovgu.featureide.featurehouse.meta;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.net.URL;
import java.nio.charset.Charset;
import java.util.AbstractList;
import java.util.ArrayList;
import java.util.LinkedList;
import java.util.Scanner;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IncrementalProjectBuilder;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.FileLocator;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Path;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.StructuredSelection;
import org.eclipse.ui.IObjectActionDelegate;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.internal.util.BundleUtility;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.featurehouse.FeatureHouseComposer;
import de.ovgu.featureide.featurehouse.FeatureHouseCorePlugin;
import de.ovgu.featureide.fm.core.FMCorePlugin;

/**
 * Builds the meta product via FeatureHouse. 
 *
 * @author Jens Meinicke
 */
@SuppressWarnings("restriction")
public class VerifyProductAction implements IObjectActionDelegate {

	private final static String VERIFIKATION_MARKER = "de.ovgu.featureide.featurehouse.meta.verificationmarker";

	private boolean errorOccured = false;

	private StructuredSelection selection;

	private Process process;
	
	private static ArrayList<String> command = new ArrayList<String>();
	static {
		command.add(getCommand("monkey.exe", "MonKeY"));
		command.add("-batch");
		command.add("-nosplash");
//		command.add("-mtcontract"); // Method Treatment Contract
	//	command.add("-nowindow");
	//	command.add("-rounds");
	//	command.add("10");
	//	command.add("-h");			// displays all commands
		command.add("-bc");
		command.add(getCommand("JavaRedux", "JavaRedux"));
		command.add("-out");
	};

	private static String getCommand(String pathName, String toolName) {
		URL url = BundleUtility.find(FeatureHouseCorePlugin.getDefault().getBundle(), "lib/monkey/" + pathName);
		try {
			url = FileLocator.toFileURL(url);
		} catch (IOException e) {
			FeatureHouseCorePlugin.getDefault().logError(e);
		}
		Path path = new Path(url.getFile());
		String library = path.toOSString();
		if (!path.isAbsolute()) {
			FeatureHouseCorePlugin.getDefault().logWarning(library + " is not an absolute path. " +
					toolName + " can not be found.");
		}
		if (!path.isValidPath(library)) {
			FeatureHouseCorePlugin.getDefault().logWarning(library + " is no valid path. " +
					toolName + " can not be found.");
		}
		return library;
	}
	
	private static final String TRUE = "true";
	private static final String FALSE = "false";
	
	void verifyProduct(boolean value, IProject project) {
		try {
			project.setPersistentProperty(FeatureHouseComposer.VERIFY_PRODUCT, value ? TRUE : FALSE);
		} catch (CoreException e) {
			FMCorePlugin.getDefault().logError(e);
		}
	}
	
	
	@Override
	public void run(IAction action) {
		if (selection == null) {
			return;
		}
		final LinkedList<IProject> projects = new LinkedList<IProject>();
		for (Object o : selection.toList()) {
			if (o instanceof IProject) {
				projects.add((IProject)o);
			}
		}
		
		if (projects.isEmpty()) {
			return;
		}
		
		Job job = new Job("Verify") {
			int verified = 0;
			@Override
			public IStatus run(final IProgressMonitor monitor) {
				monitor.beginTask("Verify product", projects.size());
				long completeTime = System.currentTimeMillis();
				for (IProject project : projects) {
					if (monitor.isCanceled()) {
						break;
					}
					
					monitor.subTask(project.getName());
					long time = System.currentTimeMillis();
					
					if (CorePlugin.getFeatureProject(project) != null) {
						try {
							verifyProduct(true, project);
							project.build(IncrementalProjectBuilder.FULL_BUILD, null);
							verifyProduct(false, project);
						} catch (CoreException e) {
							FeatureHouseCorePlugin.getDefault().logError(e);
						}
						verified++;
						time = System.currentTimeMillis() - time;
						FeatureHouseCorePlugin.getDefault().logInfo("Product \"" + project.getName() + "\" built in " + (time-verificationTime) + 
								"ms and verified in " + verificationTime + "ms.");
						monitor.worked(1);
					} else {
						runMonkey(project);
						if (errorOccured) {
							FeatureHouseCorePlugin.getDefault().logInfo("Could not verify \"" + ((IProject)project).getName() + "\".");
							errorOccured = false;
							monitor.worked(1);
							continue;
						}
						verified++;
						time = System.currentTimeMillis() - time;
						FeatureHouseCorePlugin.getDefault().logInfo("Product \"" + ((IProject)project).getName() + "\" verified in " + time + "ms.");
						monitor.worked(1);
					}
				}
				
				if (projects.size() > 1) {
					completeTime = System.currentTimeMillis() - completeTime;
					FeatureHouseCorePlugin.getDefault().logInfo(verified + " of " + projects.size() + " products verified in " + completeTime + "ms.");
				}
				return Status.OK_STATUS;
			}
		};
		job.setPriority(Job.LONG);
		job.schedule();
	}
	
	boolean run = true;

	private static long verificationTime;
	public void runMonkey(IProject project) {
		verificationTime = System.currentTimeMillis();
		
		IFeatureProject featureProject = CorePlugin.getFeatureProject(project);
		try {
			project.deleteMarkers(VERIFIKATION_MARKER, false, IResource.DEPTH_INFINITE);
		} catch (CoreException e) {
			FeatureHouseCorePlugin.getDefault().logError(e);
		}

		LinkedList<String> command = new LinkedList<String>(VerifyProductAction.command);
		IFolder results = ((IProject)project).getFolder("results");
		if (!results.exists()) {
			try {
				results.create(true, true, null);
				results.refreshLocal(IResource.DEPTH_ZERO, null);
			} catch (CoreException e) {
				FeatureHouseCorePlugin.getDefault().logError(e);
			}
		}
		command.add(results.getLocation().toOSString());
		IFolder src = featureProject != null ? featureProject.getBuildFolder() : ((IProject)project).getFolder("src");
		command.add(src.getLocation().toOSString());
		Job destroyer = null;
		try {
			run = true;
			/** With this job MonKeY can be canceled **/
			destroyer = new Job("MonKeY") {
				@Override
				public IStatus run(final IProgressMonitor monitor) {
					synchronized (this) {
						while (run) {
							if (monitor.isCanceled()) {
								process.destroy();
								FeatureHouseCorePlugin.getDefault().logInfo("destroied");
								return Status.OK_STATUS;
							}
							try {
								wait(100);
							} catch (InterruptedException e) {
								FeatureHouseCorePlugin.getDefault().logError(e);
							}
						}
					}
					return Status.OK_STATUS;
				}
			};
			destroyer.setPriority(Job.SHORT);
			destroyer.schedule();
		
			process(command, project);
			verificationTime = System.currentTimeMillis() - verificationTime;
			
			createMarkers(project);
		} finally {
			run = false;
			try {
				if (destroyer != null) {
					destroyer.join();
				}
			} catch (InterruptedException e) {
				FeatureHouseCorePlugin.getDefault().logError(e);
			}
		}
	}
	
	protected LinkedList<String> openProofs = new LinkedList<String>();

	private void process(AbstractList<String> command, IProject project) {
		errorOccured = false;
		openProofs.clear();
		ProcessBuilder processBuilder = new ProcessBuilder(command);
		BufferedReader input = null;
		BufferedReader error = null;
		try {
			process = processBuilder.start();
			 input = new BufferedReader(new InputStreamReader(
					process.getInputStream(), Charset.availableCharsets().get("UTF-8")));
			 error = new BufferedReader(new InputStreamReader(
					process.getErrorStream(), Charset.availableCharsets().get("UTF-8")));
			boolean x = true;
			while (x) {
				try {
					String line;
					while ((line = input.readLine()) != null) {
						if (line.contains("OPEN")) {
							FeatureHouseCorePlugin.getDefault().logWarning(line);
							openProofs.add(line);
//							createMarker(line, project);
						} else if (line.contains("CLOSED")) {
//							FeatureHouseCorePlugin.getDefault().logInfo(line);
						} else if (line.contains("Invalid parameters")) {
							errorOccured = true;
							FeatureHouseCorePlugin.getDefault().logError(line, null);
						} else if (line.contains("Warning")) {
							FeatureHouseCorePlugin.getDefault().logWarning(line);
						}
						
//						else FeatureHouseCorePlugin.getDefault().logWarning(line);
					}
					while ((line = error.readLine()) != null) {
						if (line.startsWith("Could not resolve")) {
							FeatureHouseCorePlugin.getDefault().logError(line, null);
							errorOccured = true;
						} else if (line.contains("expecting") && line.contains("line")) {
							FeatureHouseCorePlugin.getDefault().logError(line, null);
							errorOccured = true;
						} else if (line.contains("unexpected token")) {
							FeatureHouseCorePlugin.getDefault().logError(line, null);
							errorOccured = true;
						}
						
//						else FeatureHouseCorePlugin.getDefault().logWarning(line);
					}
					try {
						process.waitFor();
					} catch (InterruptedException e) {
						FeatureHouseCorePlugin.getDefault().logError(e);
					}
					int exitValue = process.exitValue();
					if (exitValue != 0) {
						throw new IOException(
								"The process doesn't finish normally (exit="
										+ exitValue + ")!");
					}
					x = false;
				} catch (IllegalThreadStateException e) {
					FeatureHouseCorePlugin.getDefault().logError(e);
				}
			}
		} catch (IOException e) {
			FeatureHouseCorePlugin.getDefault().logError(e);
		}finally{
			try {
				if(input!=null)input.close();
			} catch (IOException e) {
				FeatureHouseCorePlugin.getDefault().logError(e);
			} finally {
				if(error!=null)
					try {
						error.close();
					} catch (IOException e) {
						FeatureHouseCorePlugin.getDefault().logError(e);
					}
			}
		}
	}
	private final static String MESSAGE = "Proof is OPEN";
	
	private ArrayList<IFile> files = new ArrayList<IFile>();
	private ArrayList<Integer> lines = new ArrayList<Integer>();

	private void createMarkers(final IProject project) {
		files.clear();
		lines.clear();
		for (String line : openProofs) {
			String proof = line.substring(line.indexOf('"') + 1);
			proof = proof.substring(0, proof.indexOf('"'));
			
			// TODO metods with parameters, if there are multiple methods with the same name
			String file = proof.substring(0, proof.indexOf('#')) + ".java";
			String method = proof.substring(proof.indexOf('#') + 1);
			
			try {
				project.getFolder("src").refreshLocal(IResource.DEPTH_ZERO, null);
			} catch (CoreException e1) {
				FeatureHouseCorePlugin.getDefault().logError(e1);
			}
			IFile res = findMember(project.getFolder("src"), file);
			try {
				res.refreshLocal(IResource.DEPTH_ZERO, null);
			} catch (CoreException e) {
				FeatureHouseCorePlugin.getDefault().logError(e);
			}
			int lineNr = findLine(res, method);
			if (hasSameMarker(MESSAGE, lineNr, res)) {
				return;
			}
			
			files.add(res);
			lines.add(lineNr);
		}
		for (int i = 0; i < files.size();i++) {
			IFile res = files.get(i);
			int lineNr = lines.get(i);
			try {
				IMarker newMarker = res.createMarker(VERIFIKATION_MARKER);
				res.refreshLocal(IResource.DEPTH_ZERO, null);
				newMarker.setAttribute(IMarker.LINE_NUMBER, lineNr);
				newMarker.setAttribute(IMarker.MESSAGE, MESSAGE);
				newMarker.setAttribute(IMarker.SEVERITY, IMarker.SEVERITY_WARNING);
				res.refreshLocal(IResource.DEPTH_ZERO, null);
			} catch (CoreException e) {
				FeatureHouseCorePlugin.getDefault().logError(e);
			}
			
		}
	}
			
	/**
	 * Checks if the file already the given marker.
	 */
	private boolean hasSameMarker(String message, int line, IFile file) {
		try {
			IMarker[] markers = file.findMarkers(null, true, IResource.DEPTH_INFINITE);
			for (IMarker m : markers) {
				if (m.getAttribute(IMarker.LINE_NUMBER, -1) == line) {
					if (m.getAttribute(IMarker.MESSAGE, "xxx").equals(message)) {
						return true;
					}
				}
			}
		} catch (CoreException e) {

		}
		return false;
	}

	private int findLine(IFile file, String method) {
		method = method.substring(0, method.indexOf('('));
		Scanner scanner = null;
		try {
			
			scanner = new Scanner(file.getContents(), "UTF-8");
			int line = 1;
			int foundLine = 0;
			boolean found = false;
			while (scanner.hasNext()) {
				String text = scanner.nextLine();
				if (found) {
					if (text.contains("{")) {
						if (text.contains(";")) {
							if (text.indexOf('{') < text.indexOf(';')) {
								return foundLine;
							} else {
								found = false;
							}
						} else {
							return foundLine;
						}
					} else {
						if (text.contains(";")) {
							found = false;
						} else {
							
						}
					}
				} else if (text.matches("[\\w,\\W]* " + method + "\\s*\\([\\W,\\w]*")) {
					found = true;
					foundLine = line;
					if (text.contains("{")) {
						if (text.contains(";")) {
							if (text.indexOf('{') < text.indexOf(';')) {
								return line;
							} else {
								found = false;
							}
						} else {
							return line;
						}
					} else {
						if (text.contains(";")) {
							found = false;
						} else {
							
						}
					}
				}
				line++;
			}
		} catch (CoreException e) {
			FeatureHouseCorePlugin.getDefault().logError(e);
		}  finally {
			if(scanner!=null) {
				scanner.close();
			}
		}
		return -1;
	}

	private IFile findMember(IFolder folder, String file) {
		try {
			for (IResource res : folder.members()) {
				if (res instanceof IFile) {
					if (file.equals(res.getName())) {
						return (IFile)res;
					}
				} else if (res instanceof IFolder) {
					IFile iFile = findMember((IFolder)res, file);
					if (iFile != null) {
						return iFile;
					}
				}
			}
		} catch (CoreException e) {
			FeatureHouseCorePlugin.getDefault().logError(e);
		}
		return null;
	}

	@Override
	public void selectionChanged(IAction action, ISelection selection) {
		if (selection == null || !(selection instanceof StructuredSelection)) {
			this.selection = null;
		} else {
			this.selection = ((StructuredSelection)selection);
		}
	}

	@Override
	public void setActivePart(IAction action, IWorkbenchPart targetPart) {
		
	}
}
