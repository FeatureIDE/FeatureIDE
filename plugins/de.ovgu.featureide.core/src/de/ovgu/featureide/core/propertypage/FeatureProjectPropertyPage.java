package de.ovgu.featureide.core.propertypage;

import java.io.Serializable;
import java.util.Arrays;
import java.util.Comparator;
import java.util.List;

import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.internal.core.JavaElement;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.ModifyEvent;
import org.eclipse.swt.events.ModifyListener;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Combo;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Group;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Text;
import org.eclipse.ui.dialogs.PropertyPage;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.builder.ComposerExtensionManager;
import de.ovgu.featureide.core.builder.IComposerExtension;

/**
 * At this property page you can specify composer specific settings for a
 * FeatureProject This property page specifies project specific settings
 * 
 * @author Jens Meinicke
 */
// TODO distinction between rename and move of folders
// TODO change from FeatureModelling -> Antenna : Sourcepath is not written
@SuppressWarnings("restriction")
public class FeatureProjectPropertyPage extends PropertyPage {

	private static final class ExtensionComparator implements
			Comparator<IComposerExtension>, Serializable {
		private static final long serialVersionUID = 1L;

		public int compare(IComposerExtension arg0, IComposerExtension arg1) {
			return arg0.getName().compareTo(arg1.getName());
		}
	}

	private static final String DESCRIPTION = null;
	private static final String COMPOSER_GROUP_TEXT = "Composition tool settings";
	private static final String COMPOSER_SELECTION_TEXT = "&Composition tool:";
	private static final String CONTRACT_SELECTION_TEXT = "&Contract composition:";
	private static final String COMPOSER_CONFIG_PATH = "&configurations path:";
	private static final String COMPOSER_FEATURE_PATH = "&Feature path:";
	private static final String COMPOSER_SOURCE_PATH = "&Source path:";

	private GridData gd = new GridData(GridData.FILL_BOTH);

	private static IComposerExtension[] extensions = null;
	private IProject project = null;
	private IFeatureProject featureProject = null;

	private Text sourcePath = null;
	private Text featurePath = null;
	private Text configPath = null;

	private IComposerExtension composer = null;
	private Combo composerCombo;
	private Combo contractCombo;
	private Combo metaCombo;
	private Combo toolCombo;

	private boolean canFinish = true;

	private ModifyListener listener = new ModifyListener() {

		public void modifyText(ModifyEvent e) {
			dialogChanged();
		}

	};

	public FeatureProjectPropertyPage() {

	}

	@Override
	protected Control createContents(Composite parent) {
		Composite composite = new Composite(parent, SWT.NONE);
		composite.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
		GridLayout layout = new GridLayout();
		layout.numColumns = 1;
		layout.verticalSpacing = 9;
		composite.setLayout(layout);

		if (!getProject()) {
			Label label = new Label(composite, SWT.NONE);
			label.setText("No resource selected.");
			return composite;
		}

		featureProject = CorePlugin.getFeatureProject(project);
		if (featureProject == null) {
			Label label = new Label(composite, SWT.NONE);
			label.setText("Project \"" + project.getName()
					+ "\" is no FeatureIDE project.");
			return composite;
		}

		composer = featureProject.getComposer();
		Label label = new Label(composite, SWT.NONE);
		label.setText("&Project: \t\t" + project.getName());
		label = new Label(composite, SWT.NONE);
		label.setText("&Compostion tool: " + composer.getName());
		label = new Label(composite, SWT.NONE);
		label.setText("&Contract Composition: "
				+ featureProject.getContractComposition());
		label = new Label(composite, SWT.NONE);
		label.setText("&Meta Product Generation: "
				+ featureProject.getMetaProductGeneration());
		label = new Label(composite, SWT.NONE);
		// TODO: change text
		label.setText("Composition tool: " 
				+ featureProject.getCompositionTool());
		addCompositionGroup(composite);
		return composite;
	}

	/**
	 * Gets the project of the selected resource.
	 * 
	 * @return <code>true</code> if successful
	 */
	private boolean getProject() {
		IAdaptable resource = getElement();
		if (resource instanceof JavaElement) {
			IJavaProject javaProject = ((JavaElement) resource)
					.getJavaProject();
			project = javaProject.getProject();
		} else if (resource instanceof IResource) {
			project = ((IResource) resource).getProject();
		} else {
			return false;
		}
		return true;
	}

	/**
	 * Adds the group to specify composer specific settings
	 * 
	 * @param composite
	 */
	private void addCompositionGroup(Composite composite) {
		Group compositionGroup = new Group(composite, SWT.NONE);
		compositionGroup.setText(COMPOSER_GROUP_TEXT);
		compositionGroup.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
		GridLayout layout = new GridLayout();
		layout.numColumns = 2;
		compositionGroup.setLayout(layout);

		addComposerMember(compositionGroup);
		addAllPathMember(compositionGroup);
		addContractMember(compositionGroup);
		addMetaProductMember(compositionGroup);
		addCompositionToolMember(compositionGroup);
	}

	/**
	 * Adds the composer combo box
	 * 
	 * @param group
	 */
	private void addComposerMember(Group group) {
		Label label = new Label(group, SWT.NULL);
		label.setText(COMPOSER_SELECTION_TEXT);
		composerCombo = new Combo(group, SWT.READ_ONLY | SWT.DROP_DOWN);
		composerCombo.setLayoutData(gd);

		List<IComposerExtension> composerExtensions = ComposerExtensionManager
				.getInstance().getComposers();
		extensions = new IComposerExtension[composerExtensions.size()];
		composerExtensions.toArray(extensions);
		Arrays.sort(extensions, new ExtensionComparator());

		for (IComposerExtension composerExtension : extensions) {
			composerCombo.add(composerExtension.getName());
		}

		String composer = featureProject.getComposer().getName();
		int i = 0;
		for (String item : composerCombo.getItems()) {
			if (item.equals(composer)) {
				composerCombo.select(i);
				break;
			}
			i++;
		}
		composerCombo.addModifyListener(listener);
	}

	/**
	 * Adds the composer combo box
	 * 
	 * @param group
	 */
	private void addContractMember(Group group) {
		Label label = new Label(group, SWT.NULL);
		label.setText(CONTRACT_SELECTION_TEXT);
		contractCombo = new Combo(group, SWT.READ_ONLY | SWT.DROP_DOWN);
		contractCombo.setLayoutData(gd);
		contractCombo.add(IFeatureProject.DEFAULT_CONTRACT_COMPOSITION);
		contractCombo.add("Plain Contracting");
		contractCombo.add("Contract Overriding");
		contractCombo.add("Explicit Contract Refinement");
		contractCombo.add("Consecutive Contract Refinement");

		String composer = featureProject.getContractComposition();
		refreshContractCombo(composer);
		contractCombo.addModifyListener(listener);
	}

	private void refreshContractCombo(String composer) {
		if (!this.composer.hasContractComposition()) {
			contractCombo.setEnabled(false);
			contractCombo.select(0);
		} else {
			int i = 0;
			for (String item : contractCombo.getItems()) {
				if (item.equals(composer)) {
					contractCombo.select(i);
					break;
				}
				i++;
			}
		}
	}

	private void addMetaProductMember(Group group) {
		Label label = new Label(group, SWT.NULL);
		label.setText("&Meta Product Generation");
		metaCombo = new Combo(group, SWT.READ_ONLY | SWT.DROP_DOWN);
		metaCombo.setLayoutData(gd);
		metaCombo.add(IFeatureProject.DEFAULT_META_PRODUCT_GENERATION);
		metaCombo.add("Java Pathfinder");
		String composer = featureProject.getMetaProductGeneration();
		refreshMetaCombo(composer);
		metaCombo.addModifyListener(listener);
	}
	
	private void refreshMetaCombo(String composer) {
		if (!this.composer.hasMetaProductGeneration()) {
			metaCombo.setEnabled(false);
			metaCombo.select(0);
		} else {
			int i = 0;
			for (String item : metaCombo.getItems()) {
				if (item.equals(composer)) {
					metaCombo.select(i);
					break;
				}
				i++;
			}
		}
	}
	
	// TODO: change name
	private void addCompositionToolMember(Group group) {
		Label label = new Label(group, SWT.NULL);
		label.setText("Composition tool");
		toolCombo = new Combo(group, SWT.READ_ONLY | SWT.DROP_DOWN);
		toolCombo.setLayoutData(gd);
		toolCombo.add(IFeatureProject.DEFAULT_COMPOSITION_TOOL);
		toolCombo.add("Jampack");
		String composer = featureProject.getCompositionTool();
		refreshCompositionToolCombo(composer);
		toolCombo.addModifyListener(listener);
	}
	
	// TODO: change name
	private void refreshCompositionToolCombo(String compositionTool) {
		if (!this.composer.hasCompositionTools()) {
			toolCombo.setEnabled(false);
			toolCombo.select(0);
		} else {
			int i = 0;
			for (String item : toolCombo.getItems()) {
				if (item.equals(compositionTool)) {
					toolCombo.select(i);
					break;
				}
				i++;
			}
		}
	}	
	
	/**
	 * Adds the text fields of features, source and configurations path
	 * 
	 * @param group
	 */
	private void addAllPathMember(Group group) {
		// add feature path
		featurePath = addPathMember(group, COMPOSER_FEATURE_PATH,
				featureProject.getSourceFolder(), composer.hasFeatureFolder());
		// add source path
		sourcePath = addPathMember(group, COMPOSER_SOURCE_PATH,
				featureProject.getBuildFolder(), composer.hasSourceFolder());
		// add configurations path
		configPath = addPathMember(group, COMPOSER_CONFIG_PATH,
				featureProject.getConfigFolder(), true);

	}

	/**
	 * Adds a path member with the given parameters
	 * 
	 * @param group
	 *            The group containing the member
	 * @param label
	 *            The displayed label
	 * @param folder
	 *            The associated folder
	 * @param enabeled
	 *            The status of the member
	 * @return The created text field
	 */
	private Text addPathMember(Group group, String labelText, IFolder folder,
			boolean enabeled) {
		Label label = new Label(group, SWT.NULL);
		label.setText(labelText);
		Text text = new Text(group, SWT.BORDER | SWT.SINGLE);
		text.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
		if (folder != null) {
			text.setText(folder.getProjectRelativePath().toOSString());
		}
		text.setEnabled(enabeled);
		text.addModifyListener(listener);
		return text;

	}

	@Override
	public String getDescription() {
		return DESCRIPTION;
	}

	@Override
	public boolean performOk() {
		if (!canFinish) {
			return false;
		}
		if (nothingChanged()) {
			return true;
		}
		setComposer();
		setPaths();
		setContractComposition();
		setMetaProductGeneration();
		setCompositionTool();
		try {
			/* update the FeatureProject settings */
			project.close(null);
			project.open(null);
		} catch (CoreException e) {
			CorePlugin.getDefault().logError(e);
		}
		return true;
	}

	private void setContractComposition() {
		if (!contractChanged()) {
			return;
		}

		featureProject.setContractComposition(contractCombo
				.getItem(contractCombo.getSelectionIndex()));

	}

	private boolean contractChanged() {
		return !featureProject.getContractComposition().equals(
				contractCombo.getText());

	}

	private void setMetaProductGeneration() {
		if (!metaProductChanged()) {
			return;
		}

		featureProject.setMetaProductGeneration(metaCombo
				.getItem(metaCombo.getSelectionIndex()));

	}

	private boolean metaProductChanged() {
		return !featureProject.getMetaProductGeneration().equals(
				metaCombo.getText());

	}

	// TODO: change name
	private void setCompositionTool() {
		if (!compositionToolChanged()) {
			return;
		}

		featureProject.setCompositionTool(toolCombo
				.getItem(toolCombo.getSelectionIndex()));

	}

	// TODO: change name
	private boolean compositionToolChanged() {
		return !featureProject.getCompositionTool().equals(
				toolCombo.getText());

	}
	
	
	/**
	 * Sets the composer of the feature project
	 */
	private void setComposer() {
		if (!composerChanged()) {
			return;
		}
		for (IComposerExtension c : extensions) {
			if (c.getName().equals(
					composerCombo.getItem(composerCombo.getSelectionIndex()))) {
				featureProject.setComposerID(c.getId());
			}
		}
	}

	/**
	 * Sets the paths of the feature project
	 */
	private void setPaths() {
		if (noPathChanged()) {
			return;
		}
		featureProject.setPaths(featurePath.getText(), sourcePath.getText(),
				configPath.getText());
	}

	/**
	 * @return <code>true</code> if the shown settings are equal to the old
	 */
	private boolean nothingChanged() {
		return !composerChanged() && noPathChanged() && !contractChanged() && !metaProductChanged() && !compositionToolChanged();
	}

	/**
	 * @return
	 */
	private boolean composerChanged() {
		return !featureProject.getComposer().getName()
				.equals(composerCombo.getText());
	}

	/**
	 * @return
	 */
	private boolean noPathChanged() {
		return featureProject.getSourceFolder() != null ? featureProject
				.getSourceFolder().getProjectRelativePath().toOSString()
				.equals(featurePath.getText()) : true && featureProject
				.getBuildFolder() != null ? featureProject.getBuildFolder()
				.getProjectRelativePath().toOSString()
				.equals(sourcePath.getText()) : true && featureProject
				.getConfigFolder() != null ? featureProject.getConfigFolder()
				.getProjectRelativePath().toOSString()
				.equals(configPath.getText()) : true;
	}

	@Override
	protected void performDefaults() {
		IComposerExtension composer = featureProject.getComposer();
		int i = 0;
		for (String item : composerCombo.getItems()) {
			if (item.equals(composer.getName())) {
				composerCombo.select(i);
				break;
			}
			i++;
		}
		i = 0;
		for (String item : contractCombo.getItems()) {
			if (item.equals(featureProject.getContractComposition())) {
				contractCombo.select(i);
				break;
			}
			i++;
		}
		i = 0;
		for (String item : metaCombo.getItems()) {
			if (item.equals(featureProject.getMetaProductGeneration())) {
				metaCombo.select(i);
				break;
			}
			i++;
		}
		i = 0;
		for (String item : toolCombo.getItems()) {
			if (item.equals(featureProject.getCompositionTool())) {
				toolCombo.select(i);
				break;
			}
			i++;
		}
		featurePath.setEnabled(composer.hasFeatureFolder());
		featurePath.setText(featureProject.getSourceFolder()
				.getProjectRelativePath().toOSString());
		sourcePath.setEnabled(composer.hasSourceFolder());
		sourcePath.setText(featureProject.getBuildFolder()
				.getProjectRelativePath().toOSString());
		configPath.setText(featureProject.getConfigFolder()
				.getProjectRelativePath().toOSString());
		refreshContractCombo(composerCombo.getText());
		refreshMetaCombo(metaCombo.getText());
		refreshCompositionToolCombo(toolCombo.getText());
	}

	/**
	 * Called if something at the dialog has been changed
	 */
	protected void dialogChanged() {
		for (IComposerExtension c : extensions) {
			if (c.getName().equals(
					composerCombo.getItem(composerCombo.getSelectionIndex()))) {
				c.loadComposerExtension();

				if (!c.hasContractComposition()) {
					contractCombo.select(0); // set to none
					contractCombo.setEnabled(false);
				} else {
					contractCombo.setEnabled(true);
				}
				if (c.hasFeatureFolder()) {
					featurePath.setEnabled(true);
					if (featurePath.getText().equals("")) {
						updateStatus("Define a features path.");
						return;
					}
					if (featurePath.getText().equals(configPath.getText())) {
						updateStatus("Configurations and features path should differ.");
						return;
					}
				} else {
					featurePath.setEnabled(false);
				}
				if (c.hasSourceFolder()) {
					sourcePath.setEnabled(true);
					if (sourcePath.getText().equals("")) {
						updateStatus("Define a source path.");
						return;
					}
					if (sourcePath.getText().equals(configPath.getText())) {
						updateStatus("Configurations and source path should differ.");
						return;
					}
				} else {
					sourcePath.setEnabled(false);
				}
				if (c.hasFeatureFolder() && c.hasSourceFolder()) {
					if (featurePath.getText().equals(sourcePath.getText())) {
						updateStatus("Source and features path should differ.");
						return;
					}
				}
				if (configPath.getText().equals("")) {
					updateStatus("Define a configurations path.");
					return;
				}

				updateStatus(null);
				return;
			}
		}

	}

	/**
	 * Updates the error message
	 * 
	 * @param message
	 */
	protected void updateStatus(String message) {
		setErrorMessage(message);
		if (message == null) {
			getApplyButton().setEnabled(true);
			canFinish = true;
		} else {
			getApplyButton().setEnabled(false);
			canFinish = false;
		}
	}
}
