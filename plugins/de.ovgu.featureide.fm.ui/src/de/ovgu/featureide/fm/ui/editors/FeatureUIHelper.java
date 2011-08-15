/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2011  FeatureIDE Team, University of Magdeburg
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
package de.ovgu.featureide.fm.ui.editors;

import java.beans.PropertyChangeEvent;
import java.util.WeakHashMap;

import org.eclipse.draw2d.geometry.Dimension;
import org.eclipse.draw2d.geometry.Point;
import org.eclipse.draw2d.geometry.Rectangle;

import de.ovgu.featureide.fm.core.Constraint;
import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.PropertyConstants;
import de.ovgu.featureide.fm.ui.editors.featuremodel.figures.LegendFigure;


/**
 * this is a hack to quickly associate features with dimension and size (which
 * is not available in the model). luckily these informations do not need to be
 * stored persistently.
 * 
 * @author Christian Kaestner
 */
public class FeatureUIHelper {

	private static final WeakHashMap<Feature, Point> featureLocation = new WeakHashMap<Feature, Point>();
	private static final WeakHashMap<Feature, Dimension> featureSize = new WeakHashMap<Feature, Dimension>();
	private static final WeakHashMap<Constraint, Point> constraintLocation = new WeakHashMap<Constraint, Point>();
	private static final WeakHashMap<Constraint, Dimension> constraintSize = new WeakHashMap<Constraint, Dimension>();
	private static Dimension legendSize= new Dimension();
	private static LegendFigure legendFigure;
	private static boolean hasVerticalLayout;
	private static boolean showHiddenFeatures = true;
	
	public static Dimension getLegendSize(){
		return legendSize;
	}
	
	public static boolean showHiddenFeatures(){
		return showHiddenFeatures;
	}
	public static void showHiddenFeatures(boolean b){
		showHiddenFeatures = b;
	}
	
	public static void setLegendSize(Dimension dim){
		legendSize = dim;
	}
	public static Point getLocation(Feature feature) {
		return featureLocation.get(feature);
	}

	public static void setLocation(Feature feature, Point newLocation) {
		Point oldLocation = getLocation(feature);
		feature.setNewLocation(newLocation);
		if (newLocation == null || newLocation.equals(oldLocation))
			return;
		featureLocation.put(feature, newLocation);
		fireLocationChanged(feature, oldLocation, newLocation);
	}
	
	public static void setTemporaryLocation(Feature feature, Point newLocation) {
		Point oldLocation = getLocation(feature);
		if (newLocation == null || newLocation.equals(oldLocation))
			return;
		featureLocation.put(feature, newLocation);
		fireLocationChanged(feature, oldLocation, newLocation);
	}

	public static Dimension getSize(Feature feature) {
		return featureSize.get(feature);
	}

	public static void setSize(Feature feature, Dimension size) {
		featureSize.put(feature, size);
	}

	public static Rectangle getBounds(Feature feature) {
		return new Rectangle(getLocation(feature), getSize(feature));
	}
	public static Rectangle getBounds(Constraint constraint) {
		return new Rectangle(getLocation(constraint), getSize(constraint));
	}
	private static void fireLocationChanged(Feature feature, Point oldLocation,
			Point newLocation) {
		PropertyChangeEvent event = new PropertyChangeEvent(feature,
				PropertyConstants.LOCATION_CHANGED, oldLocation, newLocation);
		feature.fire(event);
	}

	public static Point getReferencePoint(Feature feature) {
		return getBounds(feature).getCenter();
	}

	public static Point calculateReferencePoint(Feature feature,
			Point newLocation) {
		return new Rectangle(newLocation, getSize(feature)).getCenter();
	}
	
	public static Point getSourceLocation(Feature feature) {
		Feature parentFeature = feature;
		boolean parentFeatureHidden = false;
		while(!parentFeature.isRoot()){
			parentFeature=parentFeature.getParent();
			if(parentFeature.isHidden())
				parentFeatureHidden=true;
		}
		if((feature.isHidden()||parentFeatureHidden) && !showHiddenFeatures){
				return getTargetLocation(feature.getParent());			
		}
		return getSourceLocation(getBounds(feature));
	}

	public static Point getSourceLocation(Feature feature, Point newLocation) {
		return getSourceLocation(new Rectangle(newLocation, getSize(feature)));
	}

	private static Point getSourceLocation(Rectangle bounds) {		
		if(hasVerticalLayout){
			return new Point(bounds.getLeft().x, ( bounds.bottom() + bounds.getTop().y ) /2);
		} else {
			return new Point(bounds.getCenter().x, bounds.y);		
		}
	}

	public static Point getTargetLocation(Feature feature) {
		Rectangle bounds = getBounds(feature);
		if(hasVerticalLayout){
			return new Point(bounds.getRight().x, ( bounds.bottom() + bounds.getTop().y ) /2);
		} 
		
		return new Point(bounds.getCenter().x, bounds.bottom() - 1);		
		
	}
	
	public static void setShowHiddenFeature(boolean showHiddenFeature) {
		showHiddenFeatures = showHiddenFeature; 
	}
	
	public static boolean getShowHiddenFeature() {
		return showHiddenFeatures; 
	}
	
	public static void setVerticalLayoutBounds(boolean isVerticalLayout) {
		hasVerticalLayout = isVerticalLayout; 
	}
	public static boolean hasVerticalLayout() {
		return hasVerticalLayout; 
	}
	
	public static Dimension getSize(Constraint constraint) {
		return constraintSize.get(constraint);
	}

	public static void setSize(Constraint constraint, Dimension size) {
		constraintSize.put(constraint, size);
	}

	public static Point getLocation(Constraint constraint) {
		return constraintLocation.get(constraint);
	}

	public static void setLocation(Constraint constraint, Point newLocation) {
		Point oldLocation = getLocation(constraint);
		if (newLocation == null || newLocation.equals(oldLocation))
			return;
		constraintLocation.put(constraint, newLocation);
		fireLocationChanged(constraint, oldLocation, newLocation);
		constraint.setLocation(newLocation);
	}

	private static void fireLocationChanged(Constraint constraint,
			Point oldLocation, Point newLocation) {
		PropertyChangeEvent event = new PropertyChangeEvent(constraint,
				PropertyConstants.LOCATION_CHANGED, oldLocation, newLocation);
		constraint.fire(event);

	}

	public static void setLegendFigure(LegendFigure figure){
		legendFigure=figure;
	}
	public static LegendFigure getLegendFigure() {
		return legendFigure;
	}

}
