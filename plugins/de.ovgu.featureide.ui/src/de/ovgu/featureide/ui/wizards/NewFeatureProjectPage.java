/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2010  FeatureIDE Team, University of Magdeburg
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program. If not, see http://www.gnu.org/licenses/.
 *
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.ui.wizards;

import java.util.Arrays;
import java.util.Comparator;
import java.util.List;

import org.eclipse.jface.wizard.WizardPage;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.ModifyEvent;
import org.eclipse.swt.events.ModifyListener;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Combo;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Group;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Text;

import de.ovgu.featureide.core.builder.ComposerExtensionManager;
import de.ovgu.featureide.core.builder.IComposerExtension;


/**
 * A dialog page for creating FeatureIDE projects.
 * 
 * @author Marcus Leich
 */
public class NewFeatureProjectPage extends WizardPage {

	private IComposerExtension composerExtension = null;
	private IComposerExtension[] extensions = null;
	
	private Text sourcePath,configsPath,buildPath;
	
	private Composite container;
	private Combo toolCB;
	protected GridData gd = new GridData(GridData.FILL_HORIZONTAL);
	private GridLayout layout = new GridLayout();
	protected Group pathGroup;
	
	protected NewFeatureProjectPage() {
		super("");
		setTitle("Select a composer");
		setDescription("Creates a FeatureIDE project");
	}
	
	public void createControl(Composite parent) {
		container = new Composite(parent, SWT.NULL);
	    final GridLayout gridLayout = new GridLayout();
	    gridLayout.numColumns = 1;
	    container.setLayout(gridLayout);
	    setControl(container);
	    
	    Group toolGroup = new Group(container, SWT.NONE);
		toolGroup.setText("Composer Selection:");
		toolGroup.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
		GridLayout projGridLayout = new GridLayout();
		projGridLayout.numColumns = 2;
		toolGroup.setLayout(projGridLayout);
		
		final Label helloLabel = new Label(toolGroup, SWT.NONE);
		GridData gridData = new GridData(GridData.FILL_BOTH);
		gridData.horizontalSpan = 2;
		helloLabel.setLayoutData(gridData);
		helloLabel.setText("Please select a composer from the selection below.");
		
	    Label label = new Label(toolGroup, SWT.NONE);
	    label.setText("Composers:");
	    toolCB = new Combo(toolGroup, SWT.READ_ONLY | SWT.DROP_DOWN);
	    toolCB.setLayoutData(new GridData(GridData.FILL_BOTH));
	    
	    final Label descriptionLabel = new Label(toolGroup, SWT.NONE);
	    GridData gridData2 = new GridData(GridData.FILL_BOTH);
		gridData2.horizontalSpan = 2;
	    descriptionLabel.setLayoutData(gridData2);
	    
	    String descriptionString = "Possible choices are:\n\n";
	    List<IComposerExtension> composerExtensions = ComposerExtensionManager.getInstance().getComposers();
	    extensions = new IComposerExtension[composerExtensions.size()]; 
	    composerExtensions.toArray(extensions);
	    Arrays.sort(extensions, new Comparator<IComposerExtension> () {
			public int compare(IComposerExtension arg0, IComposerExtension arg1) {
				return arg0.getName().compareTo(arg1.getName());
			}
	    });
	    
		for (IComposerExtension composerExtension : extensions) {
			descriptionString += composerExtension.getName() + ": " + composerExtension.getDescription() + "\n";
			toolCB.add(composerExtension.getName());
		}
		if (ComposerExtensionManager.getInstance().getComposers().size() == 0) {
			descriptionString = "No composition engines installed.";
			setDescription(descriptionString);
			toolCB.setEnabled(false);
		}
		descriptionLabel.setText(descriptionString);
		toolCB.addModifyListener(new ModifyListener() {
			public void modifyText(ModifyEvent e) {
				composerExtension = extensions[toolCB.getSelectionIndex()];
			}
		});
		toolCB.select(0);
		
		//Path Group
		pathGroup = new Group(container, SWT.NONE);
		layout.numColumns = 2;
		layout.verticalSpacing = 9;
		pathGroup.setText("Path Specification:");
		pathGroup.setLayoutData(gd);
		pathGroup.setLayout(layout);
		
		String tooltip = "Sets the path of composed files.";
		label = new Label(pathGroup, SWT.NULL);
		label.setText("&Source Path:");
		label.setToolTipText(tooltip);
		buildPath = new Text(pathGroup, SWT.BORDER | SWT.SINGLE);
		buildPath.setLayoutData(gd);
		buildPath.setText("src");
		buildPath.setToolTipText(tooltip);
		
		tooltip = "Sets the path of featurefolders.";
		label = new Label(pathGroup, SWT.NULL);
		label.setText("&Feature Path:");
		label.setToolTipText(tooltip);
		sourcePath = new Text(pathGroup, SWT.BORDER | SWT.SINGLE);
		sourcePath.setLayoutData(gd);
		sourcePath.setText("features");
		sourcePath.setToolTipText(tooltip);
		
		tooltip = "Sets the path of configurationfiles.";
		label = new Label(pathGroup, SWT.NULL);
		label.setText("&Configurations Path:");
		label.setToolTipText(tooltip);
		configsPath = new Text(pathGroup, SWT.BORDER | SWT.SINGLE);
		configsPath.setLayoutData(gd);
		configsPath.setText("configs");
		configsPath.setToolTipText(tooltip);
		
		addListeners();
	}	
	
	public IComposerExtension getCompositionTool() {
		return composerExtension;
	}
	
	public boolean hasCompositionTool() {
		return composerExtension != null;
	}
	
	private void addListeners() {
		toolCB.addModifyListener(new ModifyListener() {
			
			@Override
			public void modifyText(ModifyEvent e) {
				dialogChanged();
			}
		});
		
		sourcePath.addModifyListener(new ModifyListener() {
			
			@Override
			public void modifyText(ModifyEvent e) {
				dialogChanged();
			}
		});
		
		buildPath.addModifyListener(new ModifyListener() {
			
			@Override
			public void modifyText(ModifyEvent e) {
				dialogChanged();
			}
		});
		
		configsPath.addModifyListener(new ModifyListener() {
	
			@Override
			public void modifyText(ModifyEvent e) {
				dialogChanged();
			}
		});
	}
	
	protected void dialogChanged() {
		resetPathGroup();
		getCompositionTool().initialize(null);
		getCompositionTool().editProjectWizard(sourcePath, configsPath, buildPath);
		
		if (isEnabled(sourcePath) && isEnabled(configsPath) &&
				getSourcePath().equals(getEquationsPath())) {
			updateStatus("Source Path equals Configurations Path.");
			return;
		}
		if (isEnabled(sourcePath) && isEnabled(buildPath) &&
				getSourcePath().equals(getBuildPath())) {
			updateStatus("Source Path equals Build Path.");
			return;
		}
		if (isEnabled(buildPath) && isEnabled(configsPath) && 
				getBuildPath().equals(getEquationsPath())) {
			updateStatus("Build Path equals Configurations Path.");
			return;
		}
		if (isEnabled(sourcePath) && isPathEmpty(getSourcePath(), "Source"))return;
		if (isEnabled(buildPath) && isPathEmpty(getBuildPath(), "Build"))return;
		if (isEnabled(configsPath) && isPathEmpty(getEquationsPath(), "Equations"))return;
		
		if (isEnabled(sourcePath) && isInvalidPath(getSourcePath(), "Source"))return;
		if (isEnabled(buildPath) && isInvalidPath(getBuildPath(), "Build"))return;
		if (isEnabled(configsPath) && isInvalidPath(getEquationsPath(), "Equations"))return;
		
		updateStatus(null);
	}

	private boolean isEnabled(Text text) {
		if (text.isEnabled() && text.isVisible()) {
			return true;
		}
		return false;
	}
	private void resetPathGroup() {
		sourcePath.setEnabled(true);
		configsPath.setEnabled(true);
		buildPath.setEnabled(true);
	}

	protected boolean isPathEmpty(String path, String name) {
		if (path.length() == 0) {
			updateStatus(name + " Path must be specified.");
			return true;
		}
		return false;
	}
	protected boolean isInvalidPath(String path, String name) {
		if (path.contains("*")
				|| path.contains("?")
				|| path.startsWith(".")
				|| path.endsWith(".")
				|| path.contains("//")
				|| path.endsWith("/")
				|| path.endsWith("/")
				|| path.contains("/.")
				|| path.contains("./")
				|| path.contains("<")
				|| path.contains(">")
				|| path.contains("|")
				|| path.contains(""+'"')) {
			updateStatus(name + " Path must be valid");
			return true;
		}
		return false;
	}
	
	protected void updateStatus(String message) {
		setErrorMessage(message);
		setPageComplete(message == null);
	}
	
	public String getSourcePath() {
		return sourcePath.isEnabled() ? sourcePath.getText() : "";
	}
	
	public String getEquationsPath() {

		return configsPath.isEnabled() ? configsPath.getText() : "";

	}
	
	public String getBuildPath() {
		return buildPath.isEnabled() ? buildPath.getText() : "";
	}

}
