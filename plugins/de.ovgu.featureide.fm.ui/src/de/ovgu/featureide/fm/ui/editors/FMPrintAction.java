/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2013  FeatureIDE team, University of Magdeburg, Germany
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
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.fm.ui.editors;

import java.util.Collection;
import java.util.Iterator;

import org.eclipse.draw2d.geometry.Point;
import org.eclipse.gef.ui.actions.PrintAction;
import org.eclipse.ui.IWorkbenchPart;

import de.ovgu.featureide.fm.core.Constraint;
import de.ovgu.featureide.fm.core.FMPoint;
import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.FeatureModelLayout;

/**
 * TODO A PrintAction for the FeatureModelEditor that temporarily moves the
 * feature diagram to the top-left corner
 * 
 * @author Fabian Benduhn
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
		FeatureModelEditor fmEditor = (FeatureModelEditor) this
				.getWorkbenchPart();
		FeatureModel featureModel = fmEditor.getFeatureModel();
		FeatureModelLayout layout = featureModel.getLayout();
		int layoutOld = layout.getLayoutAlgorithm();
		
		Collection<Feature> features = featureModel.getFeatures();
		Iterator<Feature> featureIter = features.iterator();
		Point minP = FeatureUIHelper.getLocation(featureIter.next()).getCopy();
		
		move(featureModel, layout, features, featureIter, minP);
		//print
		super.run();
		moveBack(featureModel, layout, layoutOld, features, minP);
		return;
	}

	private void move(FeatureModel featureModel, FeatureModelLayout layout,
			Collection<Feature> features, Iterator<Feature> featureIter,
			Point minP) {
		layout.setLayout(0);
		while (featureIter.hasNext()) {
			Feature f = featureIter.next();
			Point p = FeatureUIHelper.getLocation(f);
			if (p.x < minP.x)
				minP.x=p.x;
			if (p.y < minP.y)
				minP.y=p.y;
		}

		moveFeatures(features, minP);
		moveConstraints(featureModel, minP);
		moveLegend(featureModel, layout, minP);
	}

	private void moveBack(FeatureModel featureModel, FeatureModelLayout layout,
			int layoutOld, Collection<Feature> features, Point minP) {
		Point minPneg = new Point(-minP.x, -minP.y);
		moveFeatures(features, minPneg);
		moveConstraints(featureModel, minPneg);
		moveLegend(featureModel, layout, minPneg);
		layout.setLayout(layoutOld);
	}

	private void moveLegend(FeatureModel featureModel,
			FeatureModelLayout layout, Point minP) {
		FMPoint legendPos = layout.getLegendPos();
		Point newLegendPos = new Point(legendPos.x - minP.x, legendPos.y
				- minP.y);
		FeatureUIHelper.getLegendFigure(featureModel).setLocation(newLegendPos);
		layout.setLegendPos(newLegendPos.x, newLegendPos.y);
	}

	private void moveConstraints(FeatureModel featureModel, Point minP) {
		for (Constraint c : featureModel.getConstraints()) {
			Point newPoint = new Point(
					FeatureUIHelper.getLocation(c).getCopy().x - minP.x,
					FeatureUIHelper.getLocation(c).getCopy().y - minP.y);
			FeatureUIHelper.setLocation(c, newPoint);
		}
	}

	private void moveFeatures(Collection<Feature> features, Point minP) {
		for (Feature f : features) {
			Point newPoint = new Point(
					FeatureUIHelper.getLocation(f).getCopy().x - minP.x,
					FeatureUIHelper.getLocation(f).getCopy().y - minP.y);
			FeatureUIHelper.setLocation(f, newPoint);
		}
	}

}
