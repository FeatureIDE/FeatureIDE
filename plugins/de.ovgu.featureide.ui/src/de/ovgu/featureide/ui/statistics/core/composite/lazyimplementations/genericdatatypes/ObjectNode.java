///* FeatureIDE - A Framework for Feature-Oriented Software Development
// * Copyright (C) 2005-2015  FeatureIDE team, University of Magdeburg, Germany
// *
// * This file is part of FeatureIDE.
// * 
// * FeatureIDE is free software: you can redistribute it and/or modify
// * it under the terms of the GNU Lesser General Public License as published by
// * the Free Software Foundation, either version 3 of the License, or
// * (at your option) any later version.
// * 
// * FeatureIDE is distributed in the hope that it will be useful,
// * but WITHOUT ANY WARRANTY; without even the implied warranty of
// * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// * GNU Lesser General Public License for more details.
// * 
// * You should have received a copy of the GNU Lesser General Public License
// * along with FeatureIDE.  If not, see <http://www.gnu.org/licenses/>.
// *
// * See http://featureide.cs.ovgu.de/ for further information.
// */
//package de.ovgu.featureide.ui.statistics.core.composite.lazyimplementations.genericdatatypes;
//
//import java.util.ArrayList;
//import java.util.LinkedList;
//import java.util.TreeSet;
//
//import de.ovgu.featureide.core.fstmodel.FSTClass;
//import de.ovgu.featureide.core.fstmodel.FSTClassFragment;
//import de.ovgu.featureide.core.fstmodel.FSTRole;
//import de.ovgu.featureide.ui.statistics.core.composite.Parent;
//
///**
// * TODO description
// * 
// * @author Schleicher Miro
// */
//public class ObjectNode extends AbstractSortModeNode {
//	
//	private ArrayList<Object> list;
//	
//	/**
//	 * @param description
//	 * @param value
//	 * @param countMap
//	 */
//	public ObjectNode(String description,  ArrayList<Object> list) {
//		super(description, null);
//		this.list = list;
//		setSorted(true);
//	}
//
//	@Override
//	public void initChildren() {		
//		if (this.children.isEmpty())
//		{
//			for (Object name : list) 
//			{
//				if(name instanceof FSTClass ){
//					Parent p = new Parent(name.toString().replaceAll("/", ".") +" : " + ((FSTClass)name).getRoles().size() , "");
//				
//					LinkedList<FSTRole> roles = ((FSTClass)name).getRoles();
//					for (FSTRole fstRole : roles) {
//						p.addChild(new Parent(fstRole.getFeature().getName().replaceAll("/", "."), fstRole));		
//					}
//					addChild(p);
//				}
//				if(name instanceof FSTClassFragment) {
//					Parent p = new Parent(((FSTClassFragment) name).getFullIdentifier().replaceAll("/", ".") +" : " + ((FSTClassFragment)name).getInnerClasses().size(), "");
//					
//					TreeSet<FSTClassFragment> roles = ((FSTClassFragment)name).getInnerClasses();
//					for (FSTClassFragment fstRole : roles) {
//						p.addChild(new Parent(fstRole.getFullIdentifier(), fstRole));		
//					}
//					addChild(p);
//				}
//						
//			}
//		}
//	}
//	
//}
