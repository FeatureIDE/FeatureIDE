package de.ovgu.featureide.ui.android.wizards;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Comparator;
import java.util.List;

import org.eclipse.core.resources.IProject;
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
import de.ovgu.featureide.core.builder.IComposerExtensionBase;
import de.ovgu.featureide.ui.wizards.NewFeatureProjectPage;

/**
 * Dialog page to add the featureIDE nature to an existing Android project.
 * 
 * @author Lars-Christian Schulz
 * @author Eric Guimatsia
 */
public class ConversionPage extends NewFeatureProjectPage {
	
	public ConversionPage(IProject p) {
		super();
		setDescription("Adds the FeatureIDE nature to Android project " + ((p != null) ? p.getName() : "") + ".");
	}
	
	@Override
	public void createControl(Composite parent) {
		Composite container = new Composite(parent, SWT.NULL);
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
	    
	    StringBuilder descriptionStringBuilder = new StringBuilder();
	    descriptionStringBuilder.append("Possible choices are:\n\n");
	    List<IComposerExtension> composerExtensions = ComposerExtensionManager.getInstance().getComposers();
	    
	    // Filter for Android compatible composers
	    List<IComposerExtension> androidCompatibleComposers = new ArrayList<IComposerExtension>();
	    for (IComposerExtension composer : composerExtensions) {
	    	if (composer.supportsAndroid()) {
	    		androidCompatibleComposers.add(composer);
	    	}
	    }
	    
	    extensions = new IComposerExtensionBase[androidCompatibleComposers.size()]; 
	    androidCompatibleComposers.toArray(extensions);
	    Arrays.sort(extensions, new Comparator<IComposerExtensionBase> () {
			public int compare(IComposerExtensionBase arg0, IComposerExtensionBase arg1) {
				return arg0.getName().compareTo(arg1.getName());
			}
	    });
	    
		for (IComposerExtensionBase composerExtension : extensions) {
			descriptionStringBuilder.append(composerExtension.getName());
			descriptionStringBuilder.append(": ");
			descriptionStringBuilder.append(composerExtension.getDescription());
			descriptionStringBuilder.append("\n");
			toolCB.add(composerExtension.getName());
		}
		
		String descriptionString = descriptionStringBuilder.toString();
		if (composerExtensions.isEmpty()) {
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
		
		String tooltip = "The Android source file path cannot be changed.";
		label = new Label(pathGroup, SWT.NULL);
		label.setText("Android Source Path:");
		label.setToolTipText(tooltip);
		Text androidSrcPath = new Text(pathGroup, SWT.BORDER | SWT.SINGLE | SWT.READ_ONLY);
		androidSrcPath.setLayoutData(gd);
		androidSrcPath.setText("src");
		androidSrcPath.setToolTipText(tooltip);
		
		tooltip = "The Android resource file path cannot be changed.";
		label = new Label(pathGroup, SWT.NULL);
		label.setText("Android Resource Files Path:");
		label.setToolTipText(tooltip);
		Text androidResPath = new Text(pathGroup, SWT.BORDER | SWT.SINGLE | SWT.READ_ONLY);
		androidResPath.setLayoutData(gd);
		androidResPath.setText("res");
		androidResPath.setToolTipText(tooltip);
		
		tooltip = "Sets the path of composed files.";
		buildLabel = new Label(pathGroup, SWT.NULL);
		buildLabel.setText("&Composed files Path:");
		buildLabel.setToolTipText(tooltip);
		buildPath = new Text(pathGroup, SWT.BORDER | SWT.SINGLE);
		buildPath.setLayoutData(gd);
		buildPath.setText("composed");
		buildPath.setToolTipText(tooltip);
		
		tooltip = "Sets the path of source files.";
		label = new Label(pathGroup, SWT.NULL);
		label.setText("&Source Path:");
		label.setToolTipText(tooltip);
		sourcePath = new Text(pathGroup, SWT.BORDER | SWT.SINGLE);
		sourcePath.setLayoutData(gd);
		sourcePath.setText("source");
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
	
	@Override
	protected void dialogChanged() {
		IComposerExtensionBase compositionTool = getCompositionTool();
		sourcePath.setEnabled(compositionTool.hasFeatureFolder());
		buildPath.setEnabled(compositionTool.hasSourceFolder());
		
		if (getSourcePath().equals("src") || getSourcePath().equals("res")) {
			updateStatus("Source path cannot be \"/src\" or \"/res\".");
			return;
		}
		if (getBuildPath().equals("src") || getBuildPath().equals("res")) {
			updateStatus("Build path cannot be \"/src\" or \"/res\".");
			return;
		}
		if (getConfigPath().equals("src") || getConfigPath().equals("res")) {
			updateStatus("Config path cannot be \"/src\" or \"/res\".");
			return;
		}
		if (getSourcePath().equals(getConfigPath())) {
			updateStatus("Source path equals configurations path.");
			return;
		}
		if (getSourcePath().equals(getBuildPath())) {
			updateStatus("Source path equals build path.");
			return;
		}
		if (getBuildPath().equals(getConfigPath())) {
			updateStatus("Build path equals configurations path.");
			return;
		}
		if (isPathEmpty(getSourcePath(), "Source")
				|| isPathEmpty(getBuildPath(), "Build")
				|| isPathEmpty(getConfigPath(), "Equations")
				|| isInvalidPath(getSourcePath(), "Source")
				|| isInvalidPath(getBuildPath(), "Build")
				|| isInvalidPath(getConfigPath(), "Equations")) {
			return;
		}
		
		updateStatus(null);
	}
}
