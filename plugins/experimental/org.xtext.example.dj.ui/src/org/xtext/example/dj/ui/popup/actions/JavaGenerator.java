package org.xtext.example.dj.ui.popup.actions;

import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IActionDelegate;
import org.eclipse.ui.IObjectActionDelegate;
import org.eclipse.ui.IWorkbenchPart;
import org.xtext.example.util.DJIdeProperties;
import org.xtext.example.util.ValidationStatus;

import djtemplates.DJStandaloneCompiler;

public class JavaGenerator implements IObjectActionDelegate {

	private Shell shell;
	private String fileName;
	private String workingPath;
	private String uriPrefix;
	
	/**
	 * Constructor for Action1.
	 */
	public JavaGenerator() {
		super();
	}

	/**
	 * @see IObjectActionDelegate#setActivePart(IAction, IWorkbenchPart)
	 */
	public void setActivePart(IAction action, IWorkbenchPart targetPart) {
		action.setEnabled(false);
		shell = targetPart.getSite().getShell();
	}

	/**
	 * @see IActionDelegate#run(IAction)
	 */
	public void run(IAction action) {
		if(DJIdeProperties.getValidationStatus() != ValidationStatus.VALIDATE_ALL) {
			if(!MessageDialog.openConfirm(shell, 
					                      "Warning: incomplete validation", 
					                      "You are not in validate all mode. The compilation of this file can terminate with " +
		                                  "errors even if they are not marked by the editor. " +
		                                  "Do you wish to continue anyway (the compilation is however in validate all mode)?")) return;
		}
		ValidationStatus marker = DJIdeProperties.getValidationStatus();
		DJIdeProperties.changeValidationStatus(ValidationStatus.VALIDATE_ALL);
		System.out.println("filename::: "+fileName);
		DJStandaloneCompiler compiler = new DJStandaloneCompiler(fileName);
		boolean errors = !(compiler.compile(workingPath, workingPath + "../src-gen/", uriPrefix));
		
		try {
			ResourcesPlugin.getWorkspace().getRoot().refreshLocal(IResource.DEPTH_INFINITE, null);
		} catch (CoreException e) {
			e.printStackTrace();
		}
		
		if(errors) {
			MessageDialog.openError(shell, "Compilation informations", "The file was compiled with errors: " + compiler.getErrorReport());
		} else {
			MessageDialog.openInformation(shell, "Compilation informations", "The file was succesfully compiled");
		}
		
		DJIdeProperties.changeValidationStatus(marker);
	}

	/**
	 * @see IActionDelegate#selectionChanged(IAction, ISelection)
	 */
	public void selectionChanged(IAction action, ISelection selection) {
		if(selection == null || selection.toString().equals("<empty selection>")) {
			action.setEnabled(false); 
			return;
		}
		System.out.println("SEL"+selection);
		fileName = toFileName(selection.toString());
		workingPath = toWorkingPath(selection.toString());
	
		uriPrefix = toUriPrefix(selection.toString());
		
		String format = getFileFormat(fileName);
		if(format == null || !format.equals("dj")) {
			action.setEnabled(false);
			return;
		}
		action.setEnabled(true);
	}
	
	/* SERVICE METHODS */
	
	private  String toFileName(String name) {
		int idx = getLastSeparatorIndex(name);
		
		if(idx == -1) return name;
		
		return name.substring(idx + 1, name.length() - 1);
	}
	
	private String toWorkingPath(String name) {
		IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
		String path = root.getLocation().toString() + "/";
		if(name == null || name.equals("")) return "";
		
		int idx = getLastSeparatorIndex(name);
		if(idx == -1) return "";
		
		return path + name.substring(3, idx) + "/";
	}
	
	private String toUriPrefix(String name) {
		int idx = name.indexOf('/');
		if(idx == -1) return "";
		
		return "platform:/resource" + name.substring(idx, name.lastIndexOf('/')) + "/";
	}
	
	private int getLastSeparatorIndex(String name) {
		int idx = name.length() - 1;
		
		while(name.charAt(idx) != '/') {
			idx--;
			if(idx < 0) return -1;
		}
		
		return idx;
	}
	
	//Returns the file format or null if name doesn't contain any file name (but a directory name).
	private String getFileFormat(String name) {
		int dotindex = name.lastIndexOf('.');
		if(dotindex == -1) {
			return null;
		} else {
			return name.substring(dotindex + 1, name.length());
		}
	}
}
