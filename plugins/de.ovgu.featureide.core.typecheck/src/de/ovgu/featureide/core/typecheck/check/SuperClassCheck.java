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
package de.ovgu.featureide.core.typecheck.check;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;

import org.sat4j.specs.TimeoutException;

import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.typecheck.TypecheckCorePlugin;
import de.ovgu.featureide.core.typecheck.parser.ClassTable;
import de.ovgu.featureide.core.typecheck.parser.ClassTableEntry;
import de.ovgu.featureide.fm.core.Feature;

/**
 * TODO description
 * 
 * @author Sönke Holthusen
 */
public class SuperClassCheck  extends AbstractCheckPlugin
{
	/*
	 * (non-Javadoc)
	 * 
	 * @see de.ovgu.featureide.core.typecheck.checks.ICheckPlugin#invokeCheck()
	 */
	@Override
	public void invokeCheck(IFeatureProject project, ClassTable class_table)
	{
		for (Feature feature : class_table.getFeatures())
		{
			for (ClassTableEntry entry : class_table.getClassesByFeature(feature.getName()))
			{
			    List<String> list  = new ArrayList<String>();
			    list.add(project.getSourcePath() + "\\" + feature.getName());
			    entry.getCompilationUnit().printIntros(list);
				String superclass = entry.getAST().superclass().fullName();
				System.out.println(entry.getClassName() + " has superclass " + superclass);
				if (class_table.contains(superclass))
				{
					HashSet<Feature> featureset = new HashSet<Feature>();
					featureset.add(feature);

					HashSet<Feature> providing_feature_set = new HashSet<Feature>();

					for (Feature providing_feature : class_table.getFeaturesByClass(superclass))
					{
						providing_feature_set.add(providing_feature);
					}

					try
					{
						if (TypecheckCorePlugin.checkImpliesDisjunct(project.getFeatureModel(), featureset, providing_feature_set))
						{
							//TODO: error marker
							//project.createBuilderMarker(entry.getClassFile(), "", 1, 0);
							System.out.println("Class " + entry.getClassName() + " in Feature " + feature.getName() + " needs Superclass "
									+ superclass + " but there is no valid Configuration which can provide it!");
						}
					}
					catch (TimeoutException e)
					{
						e.printStackTrace();
					}
				}
				else
				{
					// ignore external superclasses for now
				}
			}
		}
	}

	/* (non-Javadoc)
	 * @see de.ovgu.featureide.core.typecheck.check.ICheckPlugin#register(de.ovgu.featureide.core.typecheck.check.CheckPluginManager)
	 */
	@Override
	public void register(CheckPluginManager manager)
	{
		// TODO Auto-generated method stub
		
	}
}
