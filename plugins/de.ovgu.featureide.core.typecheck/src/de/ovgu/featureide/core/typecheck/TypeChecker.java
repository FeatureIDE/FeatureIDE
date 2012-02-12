package de.ovgu.featureide.core.typecheck;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import AST.ReferenceType;

import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.typecheck.helper.Timer;
import de.ovgu.featureide.core.typecheck.parser.ClassTable;
import de.ovgu.featureide.core.typecheck.parser.ClassTableEntry;
import de.ovgu.featureide.core.typecheck.parser.Parser;
import de.ovgu.featureide.fm.core.Feature;

public class TypeChecker
{

	private IFeatureProject _project;
	private Parser _parser;
	private ClassTable _class_table;

	public TypeChecker(IFeatureProject project)
	{
		_project = project;
		_parser = new Parser();
	}

	public void run()
	{
		System.out.println("Starting parsing project "
				+ _project.getProjectName());
		String sourcePath = _project.getSourcePath();
		Collection<Feature> features = _project.getFeatureModel()
				.getConcreteFeatures();
		List<Feature> concrete_features = new ArrayList<Feature>();

		for (Feature feature : features)
		{
			concrete_features.add(feature);
		}

		// TODO: consider the userdefined feature order
		// if (_project.getFeatureModel().isFeatureOrderUserDefined()) {
		// _parser.parse(sourcePath, _project.getFeatureModel()
		// .getFeatureOrderList());
		// } else {

		_parser.parse(sourcePath, (concrete_features));

		_class_table = _parser.getClassTable();

		// }

		// System.out.println(_class_table.dumpString());

		// for(Feature feature : features)
		// {
		// System.out.println("Classes Introduced or Refined by Feature " +
		// feature.getName());
		// for(ClassTableEntry entry :
		// _class_table.getClassesByFeature(feature.getName()))
		// {
		// System.out.println("\t" + entry.getClassName());
		// }
		// }

		// for(String class_name : _class_table.getClassNames())
		// {
		// System.out.println("Features introducing or refining class " +
		// class_name);
		// for(ClassTableEntry entry :
		// _class_table.getFeaturesByClass(class_name))
		// {
		// System.out.println("\t" + entry.getFeatureName());
		// }
		// }

		// for(ClassTableEntry entry : _class_table.getClasses())
		// {
		//
		// }
		System.out.println("Parsing finished... (" + _parser.timer.getTime()
				+ " ms)");
		System.out.println("Checking for correct subtyping...");
		checkSubTyping();
		System.out.println("Subtype checking finished...");
	}

	private void checkSubTyping()
	{
		for (String feature : _parser.getClassTable().getFeatures())
		{
			System.out.println("Feature " + feature);
			for (ClassTableEntry entry : _parser.getClassTable()
					.getClassesByFeature(feature))
			{
				String superclass = entry.getAST().superclass().fullName();
				if (_parser.getClassTable().contains(superclass))
				{
					System.out.println("\tClass " + entry.getClassName()
							+ " has local Superclass " + superclass);
					StringBuilder builder = new StringBuilder();
					for (Feature providing_feature : _parser.getClassTable()
							.getFeaturesByClass(superclass))
					{
						System.out.println("\t\tFeature " + providing_feature.getName()
								+ " can provide this Superclass");
					}
				} else
				{
					// ignore external superclasses for now
				}

			}
		}
	}
}
