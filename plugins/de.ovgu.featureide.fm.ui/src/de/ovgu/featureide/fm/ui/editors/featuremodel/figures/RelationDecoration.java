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
package de.ovgu.featureide.fm.ui.editors.featuremodel.figures;

import java.util.LinkedList;

import org.eclipse.draw2d.Ellipse;
import org.eclipse.draw2d.Graphics;
import org.eclipse.draw2d.RotatableDecoration;
import org.eclipse.draw2d.geometry.Point;
import org.eclipse.draw2d.geometry.Rectangle;

import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.ui.editors.FeatureUIHelper;
import de.ovgu.featureide.fm.ui.editors.featuremodel.GUIDefaults;


/**
 * A decoration for a feature connection that indicates its group type.
 * 
 * @author Thomas Thuem
 */
public class RelationDecoration extends Ellipse implements RotatableDecoration, GUIDefaults {
	
	private boolean fill;
	
	private Point referencePoint;

	private Feature lastChild;
	private LinkedList<Feature> children;

	public RelationDecoration(boolean fill, Feature lastChild, LinkedList<Feature> children) {
		super();
		this.fill = fill;
		this.children = children;
		this.lastChild = lastChild;
		setForegroundColor(DECORATOR_FOREGROUND);
		setBackgroundColor(DECORATOR_FOREGROUND);		
		setSize(getTargetAnchorDiameter(), getTargetAnchorDiameter()/2);
		if(!FeatureUIHelper.hasVerticalLayout()){
			setSize(getTargetAnchorDiameter(), getTargetAnchorDiameter()+10);
		}
	}
	@Override
	public void setLocation(Point p) {
		if(FeatureUIHelper.hasVerticalLayout() && !(this instanceof LegendRelationDecoration)){
			super.setLocation(p.translate(-getTargetAnchorDiameter()/2, 
					- FeatureUIHelper.getSize(lastChild.getParent()).height()/2));
		}
		else{
			if(this instanceof LegendRelationDecoration){
				super.setLocation(p.translate(-getTargetAnchorDiameter()/2,0));
			} else {
				super.setLocation(p.translate(-getTargetAnchorDiameter()/2,- 10));
			}
		}
	}
	
	public void setReferencePoint(Point p) {
		referencePoint = p;
	}
	
	@Override
	protected void fillShape(Graphics graphics) {
		if (!fill)
			return;
		
		int highestAngle1 = Integer.MAX_VALUE;
		int highestAngle2 = Integer.MIN_VALUE;
		
		Rectangle r = calculateRectangle();
		if(!(this instanceof LegendRelationDecoration)){

			if(children != null) {
				for(int i = 0; i < children.size(); i++){
					Feature temp;
					temp = this.lastChild;
					this.lastChild = children.get(i);
					if(!(this.lastChild.isHidden()&&!FeatureUIHelper.getShowHiddenFeature())){
						int angle2 = HALF_ARC ? 360 : calculateAngle(r.getCenter(), getFeatureLocation());
						int angle1 = HALF_ARC ? 180 : calculateAngle(r.getCenter(), getFeatureLocation());
						if(angle1 < highestAngle1){
							highestAngle1 = angle1;
						}
						if(angle2 > highestAngle2){
							highestAngle2 = angle2;
						} else {
							this.lastChild = temp;
						}
					}		
				}
			} else {
				highestAngle2 = HALF_ARC ? 360 : calculateAngle(r.getCenter(), getFeatureLocation());
			}
		} else {
			highestAngle2 = HALF_ARC ? 360 : calculateAngle(r.getCenter(), getFeatureLocation());
			highestAngle1 = HALF_ARC ? 180 : calculateAngle(r.getCenter(), referencePoint);
		}

		

		if(FeatureUIHelper.hasVerticalLayout() && !(this instanceof LegendRelationDecoration)){			
				graphics.fillArc(r.x+7,r.y+18,21,21,highestAngle1, highestAngle2 - highestAngle1);						
		}
		else { 
			if (this instanceof LegendRelationDecoration) {
				graphics.fillArc(r,highestAngle1, highestAngle2 - highestAngle1);
			} else {
				graphics.fillArc(r.x+7,r.y+18,21,21,highestAngle1, highestAngle2 - highestAngle1);	
			}
		}			
	}
	
	@Override
	protected void outlineShape(Graphics graphics) {
		if (fill)
			return;
		
		Rectangle r = calculateRectangle();
		r.shrink(0, 0);
		int highestAngle1 = Integer.MAX_VALUE;
		int highestAngle2 = Integer.MIN_VALUE;
		if(!(this instanceof LegendRelationDecoration)){
			if(children != null) {
				for(int i = 0; i < children.size(); i++){
					Feature temp;
					temp = this.lastChild;
					this.lastChild = children.get(i);
					if(!(this.lastChild.isHidden()&&!FeatureUIHelper.getShowHiddenFeature())){
						int angle2 = HALF_ARC ? 360 : calculateAngle(r.getCenter(), getFeatureLocation());
						int angle1 = HALF_ARC ? 180 : calculateAngle(r.getCenter(), getFeatureLocation());
						if(angle1 < highestAngle1){
							highestAngle1 = angle1;
						}
						if(angle2 > highestAngle2){
							highestAngle2 = angle2;
						} else {
							this.lastChild = temp;
						}	
					}				
				}
			} else {
				highestAngle2 = HALF_ARC ? 360 : calculateAngle(r.getCenter(), getFeatureLocation());
			}
		} else {
			highestAngle2 = HALF_ARC ? 360 : calculateAngle(r.getCenter(), getFeatureLocation());
			highestAngle1 = HALF_ARC ? 180 : calculateAngle(r.getCenter(), referencePoint);
		}
		
		if(FeatureUIHelper.hasVerticalLayout() && !(this instanceof LegendRelationDecoration)){		
				r.shrink(1, 1);
				graphics.drawArc(r.x+7,r.y+18,18,18,highestAngle1, highestAngle2 - highestAngle1);						
		}
		else { 
			if (this instanceof LegendRelationDecoration) {
				graphics.drawArc(r,highestAngle1, highestAngle2 - highestAngle1);
			} else {
				graphics.drawArc(r.x+7,r.y+18,21,21,highestAngle1, highestAngle2 - highestAngle1);		
			}
		}
	}


	 protected Point getFeatureLocation() {
		return FeatureUIHelper.getSourceLocation(lastChild);
	}
	
	protected int getTargetAnchorDiameter(){
		return TARGET_ANCHOR_DIAMETER;
	}
	private Rectangle calculateRectangle() {
		Rectangle r = Rectangle.SINGLETON;
		r.setBounds(getBounds());
		r.y -= getTargetAnchorDiameter()/2;
		r.height = getTargetAnchorDiameter();
		r.shrink(getLineWidth()+1, getLineWidth()+1);
		return r;
	}

	private int calculateAngle(Point point, Point referencePoint) {
		int dx = referencePoint.x - point.x;
		int dy = referencePoint.y - point.y;		
		return 360 - (int) Math.round(Math.atan2(dy, dx)/Math.PI*180);
	}

}
