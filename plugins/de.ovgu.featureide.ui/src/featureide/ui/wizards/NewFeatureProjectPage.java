package featureide.ui.wizards;

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

import featureide.core.builder.ComposerExtensionManager;
import featureide.core.builder.IComposerExtension;

public class NewFeatureProjectPage extends WizardPage {

	private IComposerExtension composerExtension = null;
	private IComposerExtension[] extensions = null;
	
	protected NewFeatureProjectPage() {
		super("New Jak");
		setTitle("Project");
		setDescription("Select a composer");
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
		
	    final Label label = new Label(toolGroup, SWT.NONE);
	    label.setText("Composers:");
	    final Combo toolCB = new Combo(toolGroup, SWT.READ_ONLY | SWT.DROP_DOWN);
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
			@Override
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
			@Override
			public void modifyText(ModifyEvent e) {
				composerExtension = extensions[toolCB.getSelectionIndex()];
			}
		});
		toolCB.select(0);
	}	
	
	public IComposerExtension getCompositionTool() {
		return composerExtension;
	}
	
	public boolean hasCompositionTool() {
		return composerExtension != null;
	}
}
