/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2019  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.fm.ui.wizards;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;

import org.eclipse.core.commands.operations.UndoContext;
import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.FillLayout;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;

import de.ovgu.featureide.fm.core.FeatureModelAnalyzer;
import de.ovgu.featureide.fm.core.analysis.ConstraintProperties;
import de.ovgu.featureide.fm.core.analysis.ConstraintProperties.ConstraintStatus;
import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent.EventType;
import de.ovgu.featureide.fm.core.io.manager.FeatureModelManager;
import de.ovgu.featureide.fm.core.io.manager.VirtualFeatureModelManager;
import de.ovgu.featureide.fm.ui.editors.FeatureDiagramViewer;
import de.ovgu.featureide.fm.ui.editors.IGraphicalConstraint;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeature;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeatureModel;
import de.ovgu.featureide.fm.ui.editors.elements.GraphicalFeatureModel;
import de.ovgu.featureide.fm.ui.properties.FMPropertyManager;

/**
 * A wizard page to show implicit constraints of a sub feature model. Enables automated analysis on the sub feature model to explain implicit (redundant)
 * constraints.
 *
 * @author Ananieva Sofia
 */
public class SubtreeDependencyPage extends AbstractWizardPage {

	/**
	 * The sub feature model which contains implicit constraints if there are any.
	 */
	private final IFeatureModel subtreeModel;

	/**
	 * The origin feature model which contains the sub feature model.
	 */
	private final IFeatureModel completeFm;

	private FeatureModelAnalyzer subTreeAnalyzer;

	/**
	 * Remember explanation for redundant constraint. Key = constraintIndex, Value = explanation. Used as tool tip for redundant constraint.
	 */
	public static HashMap<Integer, List<String>> redundantExpl = new HashMap<Integer, List<String>>();

	/**
	 * Constructor.
	 *
	 * @param fm The sub feature model
	 * @param completeModel The origin feature model
	 */
	public SubtreeDependencyPage(IFeatureModel fm, IFeatureModel completeModel) {
		super("Hidden Dependencies of a Submodel");
		setTitle("Hidden Dependencies of a Submodel");
		setDescription("If the selected submodel contains hidden dependencies (implicit constraints), "
			+ "they are presented below the feature model in a red border.");
		subtreeModel = fm;
		completeFm = completeModel;
		subTreeAnalyzer = null;
	}

	/**
	 * Creates a control for the dialog page. Integrates the sub feature model and uses FillLayout to fill all available space. Inserts the subtree model into a
	 * container within a wizard page. Enables automated analysis for the sub feature model and explains implicit constraints using the origin feature model.
	 *
	 * @param parent A composite which contains the feature model
	 */
	@Override
	public void createControl(Composite parent) {
		parent.setBackground(FMPropertyManager.getDiagramBackgroundColor());

		// parent composite
		final GridLayout gridLayout = new GridLayout(1, false);
		gridLayout.horizontalSpacing = 0;
		gridLayout.verticalSpacing = 0;
		gridLayout.marginHeight = 0;
		gridLayout.marginWidth = 0;
		parent.setLayout(gridLayout);

		final VirtualFeatureModelManager featureModelManager = new VirtualFeatureModelManager(subtreeModel);
		subTreeAnalyzer = featureModelManager.getPersistentFormula().getAnalyzer();
		featureModelManager.setUndoContext(new UndoContext());
		final IGraphicalFeatureModel graphicalFeatureModel = new GraphicalFeatureModel(featureModelManager);
		graphicalFeatureModel.init();
		final FeatureDiagramViewer viewer = new FeatureDiagramViewer(graphicalFeatureModel);

		final GridData gridData = new GridData();
		gridData.horizontalAlignment = SWT.FILL;
		gridData.verticalAlignment = SWT.FILL;
		gridData.grabExcessHorizontalSpace = true;
		gridData.grabExcessVerticalSpace = true;
		final Composite compositeBottom = new Composite(parent, SWT.FILL);
		compositeBottom.setLayout(new FillLayout());
		compositeBottom.setLayoutData(gridData);

		viewer.createControl(compositeBottom);
		viewer.setContents(graphicalFeatureModel);
		viewer.getControl().addControlListener(viewer.createControlListener());
		viewer.getControl().setBackground(FMPropertyManager.getDiagramBackgroundColor());

		// Reset is nessecary to removed wrong cached values
		subTreeAnalyzer.reset();
		subTreeAnalyzer.getAnalysesCollection().inheritSettings(FeatureModelManager.getAnalyzer(completeFm).getAnalysesCollection());
		subTreeAnalyzer.analyzeFeatureModel(null);

		explainImplicitConstraints(subTreeAnalyzer, graphicalFeatureModel); // explain implicit, i.e. redundant, constraints

		updateGraphicsViewer(viewer, graphicalFeatureModel);

		setPageComplete(true);
		setControl(compositeBottom);
	}

	private void updateGraphicsViewer(FeatureDiagramViewer viewer, IGraphicalFeatureModel graphicalFeatureModel) {
		for (final IGraphicalFeature f : graphicalFeatureModel.getVisibleFeatures()) {
			f.getObject().fireEvent(new FeatureIDEEvent(this, EventType.ATTRIBUTE_CHANGED, false, true));
			f.update(FeatureIDEEvent.getDefault(EventType.ATTRIBUTE_CHANGED));
		}
		for (final IGraphicalConstraint c : graphicalFeatureModel.getVisibleConstraints()) {
			c.getObject().fireEvent(new FeatureIDEEvent(this, EventType.ATTRIBUTE_CHANGED, false, true));
			c.update(FeatureIDEEvent.getDefault(EventType.ATTRIBUTE_CHANGED));
		}
		viewer.internRefresh(true);
	}

	/**
	 * Checks if implicit constraints are redundant (must be) and explains them. Sets the tool tip with explanations.
	 *
	 * @param analyzer The feature model analyzer for the sub feature model
	 * @param graphicalFeatModel The graphical feature model of the sub feature model
	 */
	private void explainImplicitConstraints(FeatureModelAnalyzer analyzer, IGraphicalFeatureModel graphicalFeatModel) {
		// iterate implicit constraints and generate explanations
		for (final IConstraint redundantC : getImplicitConstraints()) {
			final ConstraintProperties constraintProperties = subTreeAnalyzer.getConstraintProperties(redundantC);
			constraintProperties.setStatus(ConstraintStatus.IMPLICIT);
			subTreeAnalyzer.getExplanation(redundantC, FeatureModelManager.getInstance(completeFm).getPersistentFormula());

			// remember if an implicit constraint exists to adapt legend
			for (final IGraphicalConstraint gc : graphicalFeatModel.getConstraints()) {
				if (gc.getObject().equals(redundantC)) {
					gc.setConstraintImplicit(true);
					break;
				}
			}
		}

	}

	/**
	 * Returns implicit constraints for the sub feature model by iterating constraints of the origin model and the sub feature model and collecting constraints
	 * which are only present in the sub feature model but not in the origin one.
	 *
	 * @return result A list which contains implicit constraints for the subtree feature model
	 */
	private List<IConstraint> getImplicitConstraints() {
		final List<IConstraint> newConstraints = subtreeModel.getConstraints();
		final List<IConstraint> oldConstraints = completeFm.getConstraints();
		final List<IConstraint> result = new ArrayList<>();
		result.addAll(newConstraints);

		final Iterator<IConstraint> it = result.iterator();
		while (it.hasNext()) {
			final IConstraint constrNew = it.next();
			for (final IConstraint constrOld : oldConstraints) {
				if (constrOld.getNode().toRegularCNF().equals(constrNew.getNode().toRegularCNF())) {
					it.remove();
					break;
				}
			}
		}
		return result;
	}

	@Override
	public void putData() {
		abstractWizard.putData(WizardConstants.KEY_IN_FEATUREMODEL, subtreeModel);
	}

}
