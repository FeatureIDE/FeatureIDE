/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2017  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.fm.ui.editors;

import static de.ovgu.featureide.fm.core.localization.StringTable.ADD_IMPORTED_FEATURES;
import static de.ovgu.featureide.fm.core.localization.StringTable.ADD_IMPORTED_FEATURES_ALREADY_IMPORTED_WARNING;

import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import org.eclipse.draw2d.ColorConstants;
import org.eclipse.jface.dialogs.Dialog;
import org.eclipse.jface.dialogs.IDialogConstants;
import org.eclipse.jface.viewers.AbstractTreeViewer;
import org.eclipse.jface.viewers.ILabelProvider;
import org.eclipse.jface.viewers.ILabelProviderListener;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.ITreeContentProvider;
import org.eclipse.jface.viewers.ITreeSelection;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.viewers.TreePath;
import org.eclipse.jface.viewers.TreeSelection;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.graphics.Point;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.RowLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Shell;

import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.impl.MultiFeatureModel;
import de.ovgu.featureide.fm.core.base.impl.RootFeatureSet;
import de.ovgu.featureide.fm.core.io.manager.FeatureModelManager;
import de.ovgu.featureide.fm.core.io.manager.IFeatureModelManager;
import de.ovgu.featureide.fm.ui.editors.featuremodel.GUIDefaults;

/**
 * A dialog to select root features of imported models to be added to the importing model.
 *
 * @author Kevin Jedelhauser
 * @author Johannes Herschel
 */
public class AddImportedFeaturesDialog extends Dialog {

	/**
	 * Wrapper class for features of imported models that may be selected to be added. Used as child elements of the tree viewer.
	 *
	 * @author Kevin Jedelhauser
	 * @author Johannes Herschel
	 */
	public static class ImportedFeature {

		/**
		 * The model that contains the feature.
		 */
		public final MultiFeatureModel.UsedModel importedModel;
		/**
		 * The root feature that may be selected in the dialog.
		 */
		public final IFeature feature;
		/**
		 * Whether the feature is already imported.
		 */
		private final boolean alreadyImported;

		private ImportedFeature(MultiFeatureModel.UsedModel importedModel, IFeature feature, boolean alreadyImported) {
			this.importedModel = importedModel;
			this.feature = feature;
			this.alreadyImported = alreadyImported;
		}
	}

	/**
	 * Content provider for the tree viewer of the dialog. The root elements of the tree viewer are the imported models. Each model has a child element for each
	 * root feature of the model.
	 *
	 * @author Kevin Jedelhauser
	 * @author Johannes Herschel
	 */
	private class ImportedFeatureContentProvider implements ITreeContentProvider {

		@Override
		public Object[] getElements(Object inputElement) {
			return importedFeatures.keySet().toArray();
		}

		@Override
		public Object[] getChildren(Object parentElement) {
			if (parentElement instanceof MultiFeatureModel.UsedModel) {
				final MultiFeatureModel.UsedModel externalModel = (MultiFeatureModel.UsedModel) parentElement;
				return importedFeatures.get(externalModel).toArray();
			} else {
				return null;
			}
		}

		@Override
		public Object getParent(Object element) {
			if (element instanceof ImportedFeature) {
				final ImportedFeature f = (ImportedFeature) element;
				return f.importedModel;
			} else {
				return null;
			}
		}

		@Override
		public boolean hasChildren(Object element) {
			return element instanceof MultiFeatureModel.UsedModel;
		}
	}

	/**
	 * Label provider for the tree viewer of the dialog.
	 *
	 * @author Kevin Jedelhauser
	 * @author Johannes Herschel
	 */
	private class ImportedFeatureLabelProvider implements ILabelProvider {

		@Override
		public void addListener(ILabelProviderListener listener) {}

		@Override
		public void dispose() {}

		@Override
		public boolean isLabelProperty(Object element, String property) {
			return false;
		}

		@Override
		public void removeListener(ILabelProviderListener listener) {}

		@Override
		public Image getImage(Object element) {
			return null;
		}

		@Override
		public String getText(Object element) {
			if (element instanceof MultiFeatureModel.UsedModel) {
				// For models (root elements of the tree viewer), show model name and alias if present
				final MultiFeatureModel.UsedModel model = (MultiFeatureModel.UsedModel) element;
				if (model.getModelName().equals(model.getVarName())) {
					return model.getModelName();
				} else {
					return model.getModelName() + " (" + model.getVarName() + ")";
				}
			} else if (element instanceof ImportedFeature) {
				// For root features (child elements of the tree viewer), show feature name
				final ImportedFeature importedFeature = (ImportedFeature) element;
				return importedFeature.feature.getName();
			} else {
				return "";
			}
		}
	}

	/**
	 * Initial and minimum dialog size.
	 */
	private static final Point DIALOG_SIZE = new Point(500, 400);

	/**
	 * All features that can be imported, grouped by their model.
	 */
	private final Map<MultiFeatureModel.UsedModel, List<ImportedFeature>> importedFeatures;
	/**
	 * All features that can be imported, grouped by their model and their constraint dependencies.
	 */
	private final Map<MultiFeatureModel.UsedModel, Set<RootFeatureSet>> rootSets;

	private TreeViewer treeViewer;
	private Composite warningLabel;
	private Label warningText;

	/**
	 * Currently selected features, used to calculate selection changes
	 */
	private final Set<RootFeatureSet> lastSelectedFeatures = new HashSet<>();

	/**
	 * Selected features after the dialog has been closed with ok.
	 */
	private Map<MultiFeatureModel.UsedModel, Set<RootFeatureSet>> finalSelection = new HashMap<>();

	public AddImportedFeaturesDialog(Shell parentShell, IFeatureModelManager featureModelManager) {
		super(parentShell);
		setShellStyle(getShellStyle() | SWT.RESIZE);

		final IFeatureModel featureModel = featureModelManager.getSnapshot();
		if (!(featureModel instanceof MultiFeatureModel)) {
			throw new IllegalArgumentException("Feature model is not a MultiFeatureModel.");
		}

		// All imported models
		final Map<MultiFeatureModel.UsedModel, IFeatureModel> importedFeatureModels = ((MultiFeatureModel) featureModel).getExternalModels().values().stream()
				.collect(Collectors.toMap(usedModel -> usedModel, usedModel -> FeatureModelManager.getInstance(usedModel.getPath()).getSnapshot()));

		// Compute root features that can be imported
		importedFeatures = new HashMap<>();
		for (final Map.Entry<MultiFeatureModel.UsedModel, IFeatureModel> entry : importedFeatureModels.entrySet()) {
			final MultiFeatureModel.UsedModel usedModel = entry.getKey();
			final List<ImportedFeature> imported = FeatureUtils.getRoots(entry.getValue()).stream().map(root -> {
				final boolean alreadyImported = featureModel.getFeature(usedModel.getVarName() + "." + root.getName()) != null;
				return new ImportedFeature(usedModel, root, alreadyImported);
			}).collect(Collectors.toList());
			importedFeatures.put(usedModel, imported);
		}

		// Root features that can be imported, grouped by their constraint dependencies
		rootSets = new HashMap<>();
		for (final Map.Entry<MultiFeatureModel.UsedModel, IFeatureModel> entry : importedFeatureModels.entrySet()) {
			rootSets.put(entry.getKey(), RootFeatureSet.split(entry.getValue()));
		}
	}

	@Override
	protected Control createDialogArea(Composite parent) {
		final Composite composite = (Composite) super.createDialogArea(parent);

		// Create widgets
		final Label label = new Label(composite, SWT.NONE);
		label.setText("Please select the feature to be added.");

		treeViewer = new TreeViewer(composite, SWT.MULTI);
		treeViewer.setAutoExpandLevel(AbstractTreeViewer.ALL_LEVELS);
		final GridData treeLayoutData = new GridData(SWT.FILL, SWT.FILL, true, true);
		treeViewer.getControl().setLayoutData(treeLayoutData);
		treeViewer.setContentProvider(new ImportedFeatureContentProvider());
		treeViewer.setLabelProvider(new ImportedFeatureLabelProvider());

		createWarningLabel(composite);

		// Listener to automatically select and deselect root features based on constraint dependencies
		treeViewer.addSelectionChangedListener(new ISelectionChangedListener() {

			@Override
			public void selectionChanged(SelectionChangedEvent event) {
				// Compute selected features from selection
				final Set<ImportedFeature> selectedFeatures = ((List<?>) event.getStructuredSelection().toList()).stream()
						.filter(e -> e instanceof ImportedFeature).map(e -> (ImportedFeature) e).collect(Collectors.toSet());

				// Newly selected root sets/features
				final Set<RootFeatureSet> addedSets = new HashSet<>();
				for (final ImportedFeature f : selectedFeatures) {
					if (lastSelectedFeatures.stream().noneMatch(rs -> rs.getRootFeatures().contains(f.feature))) {
						addedSets.add(RootFeatureSet.find(f.feature, rootSets.get(f.importedModel)));
					}
				}
				final List<IFeature> addedFeatures = addedSets.stream().flatMap(rs -> rs.getRootFeatures().stream()).collect(Collectors.toList());

				// Newly deselected root sets/features
				final Set<RootFeatureSet> removedSets = new HashSet<>();
				for (final RootFeatureSet rs : lastSelectedFeatures) {
					for (final IFeature f : rs.getRootFeatures()) {
						if (selectedFeatures.stream().noneMatch(imported -> imported.feature == f)) {
							removedSets.add(rs);
							break;
						}
					}
				}
				final List<IFeature> removedFeatures = removedSets.stream().flatMap(rs -> rs.getRootFeatures().stream()).collect(Collectors.toList());

				// If any changes occurred, update the selection based on constraints. This triggers a second pass of this listener where no changes are
				// detected; this is handled by the else case, where the remaining dialog is updated.
				if (!addedSets.isEmpty() || !removedSets.isEmpty()) {
					// New selection based on previous selection
					final Set<TreePath> newSelection = Arrays.stream(((ITreeSelection) event.getStructuredSelection()).getPaths()).collect(Collectors.toSet());

					// Add newly selected features
					newSelection.addAll(importedFeatures.values().stream().flatMap(List::stream)
							.filter(imported -> addedFeatures.stream().anyMatch(f -> f == imported.feature))
							.map(imported -> new TreePath(new Object[] { imported.importedModel, imported })).collect(Collectors.toList()));

					// Remove deselected features
					newSelection.removeIf(path -> (path.getLastSegment() instanceof ImportedFeature)
						&& removedFeatures.stream().anyMatch(f -> f == ((ImportedFeature) path.getLastSegment()).feature));

					// Store selection for next listener pass
					lastSelectedFeatures.addAll(addedSets);
					lastSelectedFeatures.removeAll(removedSets);

					// Update selection
					final TreePath[] paths = newSelection.toArray(new TreePath[0]);
					treeViewer.setSelection(new TreeSelection(paths));
				} else {
					final boolean featuresAlreadyImported = selectedFeatures.stream().anyMatch(e -> e.alreadyImported);

					// Enable button iff selection is valid
					final Button button = getButton(IDialogConstants.OK_ID);
					if (button != null) {
						button.setEnabled((selectedFeatures.size() != 0) && !featuresAlreadyImported);
					}

					// Show warning if at least one selected feature is already imported
					warningLabel.setVisible(featuresAlreadyImported);
				}
			}
		});

		// Set input of tree viewer. Input is not needed, but must be non-null to update the viewer.
		treeViewer.setInput(new Object());

		// Mark already imported features with gray text and warning icon
		Arrays.stream(treeViewer.getTree().getItems()).flatMap(model -> Arrays.stream(model.getItems()))
				.filter(feature -> ((ImportedFeature) feature.getData()).alreadyImported).forEachOrdered(feature -> {
					feature.setForeground(ColorConstants.gray);
					feature.setImage(GUIDefaults.FM_WARNING);
				});

		applyDialogFont(composite);
		return composite;
	}

	private void createWarningLabel(Composite parent) {
		warningLabel = new Composite(parent, SWT.NONE);

		final RowLayout layout = new RowLayout();
		layout.center = true;
		layout.fill = true;
		warningLabel.setLayout(layout);
		warningLabel.setVisible(false);

		final Label icon = new Label(warningLabel, SWT.NONE);
		icon.setImage(GUIDefaults.FM_WARNING);

		warningText = new Label(warningLabel, SWT.NONE);
		warningText.setText(ADD_IMPORTED_FEATURES_ALREADY_IMPORTED_WARNING);
	}

	@Override
	protected void createButtonsForButtonBar(Composite parent) {
		super.createButtonsForButtonBar(parent);
		// Disable ok button by default
		getButton(IDialogConstants.OK_ID).setEnabled(false);
	}

	@Override
	protected void configureShell(Shell newShell) {
		super.configureShell(newShell);
		// Dialog title and minimum size
		newShell.setText(ADD_IMPORTED_FEATURES);
		newShell.setMinimumSize(DIALOG_SIZE);
	}

	@Override
	protected Point getInitialSize() {
		return DIALOG_SIZE;
	}

	@Override
	protected void okPressed() {
		// Calculate final selection when ok button is pressed
		finalSelection = new HashMap<>();
		for (final Map.Entry<MultiFeatureModel.UsedModel, Set<RootFeatureSet>> entry : rootSets.entrySet()) {
			for (final RootFeatureSet rs : entry.getValue()) {
				if (lastSelectedFeatures.contains(rs)) {
					final MultiFeatureModel.UsedModel model = entry.getKey();
					if (!finalSelection.containsKey(model)) {
						finalSelection.put(model, new HashSet<>());
					}
					finalSelection.get(model).add(rs);
				}
			}
		}

		super.okPressed();
	}

	/**
	 * @return The final selection after the dialog has been closed. Empty if the dialog has not been closed with ok (yet).
	 */
	public Map<MultiFeatureModel.UsedModel, Set<RootFeatureSet>> getFinalSelection() {
		return finalSelection;
	}
}
