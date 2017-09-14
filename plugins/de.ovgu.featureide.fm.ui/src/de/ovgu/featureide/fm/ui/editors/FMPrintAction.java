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

import java.util.Collection;
import java.util.Iterator;

import org.eclipse.draw2d.geometry.Point;
import org.eclipse.gef.ui.actions.PrintAction;
import org.eclipse.ui.IWorkbenchPart;

import de.ovgu.featureide.fm.ui.FMUIPlugin;
import de.ovgu.featureide.fm.ui.editors.featuremodel.editparts.LegendEditPart;
import de.ovgu.featureide.fm.ui.editors.featuremodel.layouts.FeatureModelLayout;

/**
 * A PrintAction for the FeatureModelEditor that temporarily moves the
 * feature diagram to the top-left corner
 * 
 * @author Fabian Benduhn
 * @author Marcus Pinnecke (Feature Interface)
 */
public class FMPrintAction extends PrintAction {

	/**
	 * @param part
	 */
	public FMPrintAction(IWorkbenchPart part) {
		super(part);

	}

	@Override
	public void run() {

		if (!(this.getWorkbenchPart() instanceof FeatureModelEditor))
			return;
		FeatureDiagramEditor fmEditor = ((FeatureModelEditor) this.getWorkbenchPart()).diagramEditor;
		IGraphicalFeatureModel featureModel = fmEditor.getGraphicalFeatureModel();
		FeatureModelLayout layout = featureModel.getLayout();
		int layoutOld = layout.getLayoutAlgorithm();

		Collection<IGraphicalFeature> features = featureModel.getFeatures();
		Iterator<IGraphicalFeature> featureIter = features.iterator();
		Point minP = featureIter.next().getLocation().getCopy();

		move(featureModel, layout, features, featureIter, minP);
		//print
		super.run();
		moveBack(featureModel, layout, layoutOld, features, minP);
		return;
	}

	private void move(IGraphicalFeatureModel featureModel, FeatureModelLayout layout, Collection<IGraphicalFeature> features,
			Iterator<IGraphicalFeature> featureIter, Point minP) {
		layout.setLayout(0);
		while (featureIter.hasNext()) {
			IGraphicalFeature f = featureIter.next();
			Point p = f.getLocation();
			if (p.x < minP.x)
				minP.x = p.x;
			if (p.y < minP.y)
				minP.y = p.y;
		}

		moveFeatures(features, minP);
		moveConstraints(featureModel, minP);
		if (!featureModel.isLegendHidden()) {
			moveLegend(featureModel, layout, minP);
		}
	}

	private void moveBack(IGraphicalFeatureModel featureModel, FeatureModelLayout layout, int layoutOld, Collection<IGraphicalFeature> features, Point minP) {
		Point minPneg = new Point(-minP.x, -minP.y);
		moveFeatures(features, minPneg);
		moveConstraints(featureModel, minPneg);
		moveLegend(featureModel, layout, minPneg);
		layout.setLayout(layoutOld);
	}

	private void moveLegend(IGraphicalFeatureModel featureModel, FeatureModelLayout layout, Point minP) {
		FeatureModelEditor editor = (FeatureModelEditor) getWorkbenchPart();
		if(editor.getEditorSite() instanceof FeatureDiagramEditor){
			FMUIPlugin.getDefault().logInfo("is feature diagramm editor");
			FeatureDiagramEditor fdEditor = (FeatureDiagramEditor) editor.getEditorSite();
			for (Object obj : fdEditor.getEditPartRegistry().values()) {
				FMUIPlugin.getDefault().logInfo("" + obj + " is of type " + obj.getClass());
				if(obj instanceof LegendEditPart) {
					FMUIPlugin.getDefault().logInfo(" is legend whohoooo! ");
					Point legendPos = layout.getLegendPos();
					Point newLegendPos = new Point(legendPos.x - minP.x, legendPos.y - minP.y);
					((LegendEditPart) obj).getFigure().setLocation(newLegendPos);
					layout.setLegendPos(newLegendPos.x, newLegendPos.y);
				}
			}
		}
	}

	private void moveConstraints(IGraphicalFeatureModel featureModel, Point minP) {
		for (IGraphicalConstraint c : featureModel.getConstraints()) {
			Point newPoint = new Point(c.getLocation().x - minP.x, c.getLocation().y - minP.y);
			c.setLocation(newPoint);
		}
	}

	private void moveFeatures(Collection<IGraphicalFeature> features, Point minP) {
		for (IGraphicalFeature f : features) {
			Point newPoint = new Point(f.getLocation().getCopy().x - minP.x, f.getLocation().getCopy().y - minP.y);
			f.setLocation(newPoint);
		}
	}

}
