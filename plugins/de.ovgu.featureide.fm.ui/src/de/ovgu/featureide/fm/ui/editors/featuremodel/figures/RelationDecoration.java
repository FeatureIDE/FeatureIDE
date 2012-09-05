/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2012  FeatureIDE team, University of Magdeburg
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
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.ui.editors.FeatureUIHelper;
import de.ovgu.featureide.fm.ui.editors.featuremodel.GUIDefaults;
import de.ovgu.featureide.fm.ui.properties.FMPropertyManager;


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
	
	private boolean vertical;
	private FeatureModel featureModel;
	
	public RelationDecoration(boolean fill, Feature lastChild, LinkedList<Feature> children) {
		super();
		this.fill = fill;
		this.children = children;
		this.lastChild = lastChild;
		setForegroundColor(FMPropertyManager.getDecoratorForgroundColor());
		setBackgroundColor(FMPropertyManager.getDecoratorForgroundColor());
		int diameter = getTargetAnchorDiameter();
		setSize(diameter, diameter/2);
		if(lastChild!=null)featureModel=lastChild.getFeatureModel();
		this.vertical = FeatureUIHelper.hasVerticalLayout(featureModel);
	}
	@Override
	public void setLocation(Point p) {
		
		if( this instanceof LegendRelationDecoration)
			super.setLocation(p.translate(-getTargetAnchorDiameter()/2,0));
		else if(vertical )
				super.setLocation(p.translate(0,-10));
		else
			super.setLocation(p.translate(-getTargetAnchorDiameter()/2,0));		
	}
	
	public void setReferencePoint(Point p) {
		referencePoint = p;
	}
	
	@Override
	protected void fillShape(Graphics graphics) {
		if (!fill)
			return;
		
		double highestAngle1 = Integer.MAX_VALUE;
		double highestAngle2 = Integer.MIN_VALUE;
		
		Rectangle r = calculateRectangle();

		if(this instanceof LegendRelationDecoration){
			highestAngle2 = HALF_ARC ? 360 : calculateAngle(r.getCenter(), getFeatureLocation());
			highestAngle1 = HALF_ARC ? 180 : calculateAngle(r.getCenter(), referencePoint);
			graphics.fillArc(r,(int) highestAngle1, (int) (highestAngle2 - highestAngle1));
		} else {
			
			if(children != null) {
				for(int i = 0; i < children.size(); i++){
					Feature temp;
					temp = this.lastChild;
					this.lastChild = children.get(i);
					if(!(this.lastChild.isHidden()&&!FeatureUIHelper.showHiddenFeatures(featureModel))){
						double angle2 = HALF_ARC ? 360 : calculateAngle(r.getCenter(), getFeatureLocation());
						double angle1 = HALF_ARC ? 180 : calculateAngle(r.getCenter(), getFeatureLocation());
						if(angle2 > 450 && !vertical) {
							highestAngle1 = 180;
						} else {
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
				}
			} else {
				highestAngle2 = HALF_ARC ? 360 : calculateAngle(r.getCenter(), getFeatureLocation());
			}
			
			r.shrink(7, 7);
	
			if (vertical){
				r.shrink(1,1);
				if(highestAngle2<270)
					graphics.fillArc(r.x-20,r.y+10,r.width,r.height,(int) 270, (int) (180));
				else
					graphics.fillArc(r.x-20,r.y+10,r.width,r.height,(int) highestAngle1, (int) (highestAngle2 - highestAngle1));	
			} else { 
				if(highestAngle1>360)
					graphics.fillArc(r,180, 180);
//				if(highestAngle2>450)
					graphics.fillArc(r,(int) highestAngle1, (int)(highestAngle2 - highestAngle1));					
//				else
//					graphics.fillArc(r,(int) highestAngle1, (int)(highestAngle2 - highestAngle1));
			}	
		}
	}
	
	@Override
	protected void outlineShape(Graphics graphics) {
		if (fill)
			return;
		
		Rectangle r = calculateRectangle();
		
		double highestAngle1 = Integer.MAX_VALUE;
		double highestAngle2 = Integer.MIN_VALUE;
		
		if(this instanceof LegendRelationDecoration){
			highestAngle2 = HALF_ARC ? 360 : calculateAngle(r.getCenter(), getFeatureLocation());
			highestAngle1 = HALF_ARC ? 180 : calculateAngle(r.getCenter(), referencePoint);
			graphics.drawArc(r,(int) highestAngle1, (int) (highestAngle2 - highestAngle1));
		} else {
			
			if(children != null) {
				for(int i = 0; i < children.size(); i++){
					Feature temp;
					temp = this.lastChild;
					this.lastChild = children.get(i);
					if(!(this.lastChild.isHidden()&&!FeatureUIHelper.showHiddenFeatures(featureModel))){
						double angle2 = HALF_ARC ? 360 : calculateAngle(r.getCenter(), getFeatureLocation());
						double angle1 = HALF_ARC ? 180 : calculateAngle(r.getCenter(), getFeatureLocation());
						if(angle2 > 450 && !vertical) {
							highestAngle1 = 180;
						} else {
						if(angle1 < highestAngle1)
							highestAngle1 = angle1;
						
						if(angle2 > highestAngle2)
							highestAngle2 = angle2;
						else 
							this.lastChild = temp;
						
						}
					}				
				}
			} else {
				highestAngle2 = HALF_ARC ? 360 : calculateAngle(r.getCenter(), getFeatureLocation());
			}
			r.shrink(7, 7);
			r.y += FeatureUIHelper.getSize(lastChild.getParent()).height/2;
			if (vertical){
				r.shrink(2,2);
				if(highestAngle2<270)
					graphics.drawArc(r.x-20,r.y,r.width,r.height,(int) 270, (int) (180));
				else
				    graphics.drawArc(r.x-20,r.y,r.width,r.height,(int) highestAngle1, (int) (highestAngle2 - highestAngle1));
			} else {  if(highestAngle1>360)
						graphics.drawArc(r.x,r.y-10,r.width,r.height,180, 180);
				      if(highestAngle2>450)
				    	  graphics.fillArc(r,(int) highestAngle1, (int)(highestAngle2 - highestAngle1));
				      else
				    	  graphics.drawArc(r.x,r.y-10,r.width,r.height,(int) (highestAngle1),  (int) (highestAngle2 - highestAngle1));
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

	private double calculateAngle(Point point, Point referencePoint) {
		int dx = referencePoint.x - point.x;
		int dy = referencePoint.y - point.y;	
		if(vertical&&!(this instanceof LegendRelationDecoration)){
			dx +=20;
			dy -=10;
		}
		return 360 - Math.round(Math.atan2(dy, dx)/Math.PI*180);
	}

}
