package de.ovgu.featureide.featurehouse.meta;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.nio.file.StandardCopyOption;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import javax.swing.JOptionPane;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.Path;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.ui.IActionDelegate;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.builder.IComposerExtension;
import de.ovgu.featureide.core.fstmodel.FSTFeature;
import de.ovgu.featureide.core.fstmodel.FSTMethod;
import de.ovgu.featureide.core.fstmodel.FSTRole;
import de.ovgu.featureide.core.mpl.InterfaceProject;
import de.ovgu.featureide.core.mpl.MPLPlugin;
import de.ovgu.featureide.core.mpl.job.ExtendedFujiSignaturesJob;
import de.ovgu.featureide.core.mpl.job.JobManager;
import de.ovgu.featureide.core.mpl.signature.ProjectSignatures;
import de.ovgu.featureide.core.mpl.signature.ProjectSignatures.SignatureIterator;
import de.ovgu.featureide.core.mpl.signature.abstr.AbstractSignature;
import de.ovgu.featureide.core.mpl.signature.filter.MethodFilter;
import de.ovgu.featureide.featurehouse.FeatureHouseCorePlugin;

public class StartProofAction implements IActionDelegate {

	final private String PATH = "D" + Path.DEVICE_SEPARATOR + "\\FeatureIDETEST\\";
	IFeatureProject featureProject = null;
	IComposerExtension composer = null;

	@Override
	public void run(IAction action) {
		
		
//		PackageExplorerPart part = PackageExplorerPart.getFromActivePerspective();
//		TreeViewer resource = part.getTreeViewer();
//		part.selectAndReveal(resource);
		
//		IWorkbench workBench = PlatformUI.getWorkbench();
//		final IWorkbenchWindow activeWindow = workBench.getActiveWorkbenchWindow();
//	    if (activeWindow != null) {
//	        final IWorkbenchPage activePage = activeWindow.getActivePage();
//	        if (activePage != null) {
//	           int i = 0;
//	        }
//	    }
		
		if (featureProject.getFSTModel() == null) {
			featureProject.getComposer().initialize(featureProject);
			featureProject.getComposer().buildFSTModel();
		}
		composer = featureProject.getComposer();
		
		final ExtendedFujiSignaturesJob fujiSignaturesJob = new ExtendedFujiSignaturesJob();

		final Object tmpObject = new Object();
		InterfaceProject intProject = MPLPlugin.getDefault().addProject(featureProject.getProject());
		fujiSignaturesJob.setProject(intProject.getProjectReference());
		Thread buildThread;
		buildThread = new Thread(new Runnable() {
			@Override
			public void run() {
				JobManager.addJob(tmpObject, fujiSignaturesJob);
				// wait for jobs to be finished
				synchronized (tmpObject) {
					try {					
						tmpObject.wait();
					} catch (InterruptedException e) {
						CorePlugin.getDefault().logError(e);
					} finally {
					}	
				}
			}
		});
		buildThread.start();
		try {
		buildThread.join();
		} catch (InterruptedException e) {
			CorePlugin.getDefault().logError(e);
		}
		

		final ProjectSignatures signatures = fujiSignaturesJob.getProjectSignatures();
		File file = null;
		String fileText = "";
		FileWriter writer;

		for (FSTFeature feat : this.featureProject.getFSTModel().getFeatures()) {
			for (FSTRole role : feat.getRoles()) {
				try {
					if (Files.notExists(Paths.get(PATH + feat.getName()))) {
						Files.createDirectories(Paths.get(PATH + feat.getName()));
					}
					System.out.println(role.getFile().getLocation().toOSString());
					final java.nio.file.Path pathNewFile = Paths.get(PATH + feat.getName() + "\\" + role.getClassFragment().getName());
					Files.copy(Paths.get(role.getFile().getLocation().toOSString()), pathNewFile, StandardCopyOption.COPY_ATTRIBUTES,  StandardCopyOption.REPLACE_EXISTING);
					file = new File(pathNewFile.toString());
					fileText = new String(Files.readAllBytes(pathNewFile));
				} catch (IOException e) {
					FeatureHouseCorePlugin.getDefault().logError(e);
				}
				
				int featureID = intProject.getFeatureID(feat.getName());
				for (FSTMethod meth : role.getClassFragment().getMethods()) {
					SignatureIterator sigIterator = signatures.createIterator();
					sigIterator.addFilter(new MethodFilter());
					while (sigIterator.hasNext()) {
						AbstractSignature curSig = sigIterator.next();
						for (int i = 0; i < curSig.getFeatureData().length; i++) {
							if (curSig.getFeatureData()[i].getId() == featureID &&
									curSig.getName().equals(meth.getName()) &&
									curSig.getType().equals(meth.getType()) &&
									curSig.getFeatureData()[i].getLineNumber() == meth.getLine()) {
								if (curSig.getFeatureData()[i].usesExternMethods()) {
									JOptionPane.showMessageDialog(null, "Die Funktion\n" + curSig.getFullName() + "\nist nicht Teil der SPL. Daher wird abgebrochen.", "Unbekannte Funktion", JOptionPane.OK_OPTION);
									return;
								}
								boolean inCurrentFeature = false;
								List<AbstractSignature> calledSignatures = curSig.getFeatureData()[i].getCalledSignatures();
								
								if (calledSignatures.size() > 0) {
									Set<AbstractSignature> tmp = new HashSet<AbstractSignature>();
									tmp.addAll(calledSignatures);
									calledSignatures = new LinkedList<AbstractSignature>();
									calledSignatures.addAll(tmp);
								}
								
								for (AbstractSignature innerAbs : calledSignatures) {
									for (int j = 0; j < innerAbs.getFeatureData().length; j++) {
										if (innerAbs.getFeatureData()[j].getId() == featureID) {
											inCurrentFeature = true;
										}
									}
									if (!inCurrentFeature) {
										try {
											writer = new FileWriter(file);
											System.out.println(innerAbs.toString());
											fileText = fileText.substring(0, fileText.lastIndexOf("\n}")) + "\n\n\t/*@\n\t@ requires_abs   " + innerAbs.getName()+"R;\n\t@ ensures_abs    "+
													innerAbs.getName()+ "E;\n\t@ assignable_abs " + innerAbs.getName()+ "A;\n\t@*/\n" + 
													"private" + innerAbs.toString() + "{" + "}\n" +
													fileText.substring(fileText.lastIndexOf("\n}") +1);
											writer.write(fileText);
											writer.close();
										} catch (IOException e) {
											FeatureHouseCorePlugin.getDefault().logError(e);
										}
									}
								}
								
							}
						}
					}	
				}		
			}
		}
	}


	@Override
	public void selectionChanged(IAction action, ISelection selection) {
		Object first = ((IStructuredSelection) selection).getFirstElement();
		if (first instanceof IProject) {
			IProject project = (IProject) first;
			IFeatureProject featureProject = CorePlugin
					.getFeatureProject(project);
			if (featureProject != null) {
				this.featureProject = featureProject;
				return;
			}
		}
	}
}
