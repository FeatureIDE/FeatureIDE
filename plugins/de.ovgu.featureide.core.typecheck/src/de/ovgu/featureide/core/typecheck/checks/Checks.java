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
package de.ovgu.featureide.core.typecheck.checks;

import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.typecheck.parser.ClassTable;
import de.ovgu.featureide.core.typecheck.parser.ClassTableEntry;
import de.ovgu.featureide.fm.core.Feature;

/**
 * TODO description
 * 
 * @author soenke
 */
public class Checks
{
	IFeatureProject _project;
	ClassTable _class_table;
	
	/**
	 * 
	 */
	public Checks(IFeatureProject project, ClassTable class_table)
	{
		_project = project;
		_class_table = class_table;
	}
	
	public void superClassCheck()
	{
		for (Feature feature : _class_table.getFeatures())
		{
			for (ClassTableEntry entry : _class_table.getClassesByFeature(feature.getName()))
			{
				String superclass = entry.getAST().superclass().fullName();
				if (_class_table.contains(superclass))
				{
					System.out.println(feature.getName() + "@" + entry.getClassName() + " has local Superclass " + superclass);
					for (Feature providing_feature : _class_table.getFeaturesByClass(superclass))
					{
						if (!feature.getName().equals(providing_feature.getName()))
						{
							System.out.println("\tFeature " + providing_feature.getName() + " can provide this Superclass");
						}
					}
				} else
				{
					// ignore external superclasses for now
				}

			}
		}

	}

}
