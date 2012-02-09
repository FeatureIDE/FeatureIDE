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
package de.ovgu.featureide.antenna.model;

import java.util.ArrayList;
import java.util.LinkedList;
import java.util.Scanner;
import java.util.Stack;
import java.util.TreeMap;
import java.util.Vector;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.CoreException;

import de.ovgu.featureide.antenna.AntennaCorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.fstmodel.FSTClass;
import de.ovgu.featureide.core.fstmodel.preprocessor.FSTDirective;
import de.ovgu.featureide.core.fstmodel.preprocessor.PPModelBuilder;

/**
 * Build the FSTModel for antenna projects.
 * 
 * @author Christoph Giesel
 * @author Marcus Kamieth
 */
public class AntennaModelBuilder extends PPModelBuilder {

	public static final String OPERATORS = "[\\s!=<>\",;&\\^\\|\\(\\)]";
	public static final String REGEX = "(//#.*" + OPERATORS + ")(%s)("
			+ OPERATORS + ")";
	
	public static final String COMMANDS = "if|ifdef|ifndef|elif|elifdef|elifndef|else|condition|define|undefine|endif";
	Pattern patternCommands = Pattern.compile("//#("+COMMANDS+")");

	public AntennaModelBuilder(IFeatureProject featureProject) {
		super(featureProject);
	}
	
	@Override
	protected void buildModelDirectives(String feature, FSTClass currentClass,
			IFile res) {
		Pattern pattern = Pattern.compile(String.format("(//#.*" + OPERATORS + ")(%s)(" + OPERATORS + "|$)", feature));
		
		TreeMap<String, LinkedList<ArrayList<String>>> directives = model.getFeaturesMap().get(feature).directives;
		LinkedList<ArrayList<String>> lines = directives.get(currentClass.getName());
		
		if (lines == null) {
			lines = new LinkedList<ArrayList<String>>();
			directives.put(currentClass.getName(), lines);
		}
		
		Scanner scanner = null;
		try {
			scanner = new Scanner(res.getContents());
			
			while (scanner.hasNext()) {
				String line = scanner.nextLine();
				Matcher matcher = pattern.matcher(line);
				
				if (matcher.find()) {
					ArrayList<String> list = new ArrayList<String>();
					line = line.replace("//#", "").trim();
					String[] splitarray = line.split("(?<=" + OPERATORS + ")");
					
					Pattern p = Pattern.compile(feature + OPERATORS + "?");

					for(String s : splitarray){
						Matcher m = p.matcher(s);
						
						if(m.matches()){
							if(s.substring(s.length()-1).matches(OPERATORS)){
								list.add(s.substring(0, s.length()-1));
								list.add(s.substring(s.length()-1));
							} else {
								list.add(s);
							}
						} else {
							if (!list.isEmpty()) {
								list.set(list.size()-1, list.get(list.size()-1).concat(s));
							} else {
								list.add(s);
							}
						}
					}
					
					lines.add(list);
				}
			}
		} catch (CoreException e) {
			AntennaCorePlugin.getDefault().logError(e);
		} finally {
			if (scanner != null)
				scanner.close();
		}
	}
	@Override
	protected ArrayList<FSTDirective> buildModelDirectivesForFile(Vector<String> lines) {
		//for preprocessor outline
		Stack<FSTDirective> directivesStack = new Stack<FSTDirective>();
		ArrayList<FSTDirective> directivesList = new ArrayList<FSTDirective>();
		
		
		for(int i=0; i < lines.size(); i++){
			String line = lines.get(i);
			
			// if line is preprocessor directive
			if (line.contains("//#")) {
				FSTDirective directive = new FSTDirective();
				
				int command = 0;
				
				if(line.contains("//#if ")){//1
					command = FSTDirective.IF;
				}else if(line.contains("//#ifdef ")){//2
					command = FSTDirective.IFDEF;
				}else if(line.contains("//#ifndef ")){//3
					command = FSTDirective.IFNDEF;
				}else if(line.contains("//#elif ")){//4
					command = FSTDirective.ELIF;
				}else if(line.contains("//#elifdef ")){//5
					command = FSTDirective.ELIFDEF;
				}else if(line.contains("//#elifndef ")){//6
					command = FSTDirective.ELIFNDEF;
				}else if(line.contains("//#else")){//7
					command = FSTDirective.ELSE;
				}else if(line.contains("//#condition ")){//8
					command = FSTDirective.CONDITION;
				}else if(line.contains("//#define ")){//9
					command = FSTDirective.DEFINE;
				}else if(line.contains("//#undefine ")){//10
					command = FSTDirective.UNDEFINE;
				}else if(line.contains("//#endif")){//11
					command = 0;
				}else{
					continue;
				}
				
				if (command != 0)
					directive.setCommand(command);
				
				Matcher m = patternCommands.matcher(line);
				line = m.replaceAll("").trim();
				
				directive.setExpression(line);
				directive.setLineNumber(i);
				
				if (command == FSTDirective.ELIF || command == FSTDirective.ELIFDEF ||
						command == FSTDirective.ELIFNDEF || command == FSTDirective.ELSE ||
						command == 0) {
					if (!directivesStack.isEmpty()) {
						directivesStack.pop();
					}
				}
				
				if (command == 0)
					continue;
				
				if(!directivesStack.isEmpty()){
					FSTDirective top = directivesStack.peek();
					top.getChildrenList().add(directive);
				} else {
					directivesList.add(directive);
				}
				
				if (command != FSTDirective.DEFINE && command != FSTDirective.UNDEFINE && command != FSTDirective.CONDITION)
					directivesStack.push(directive);
			}
		}
		return directivesList;
	}


	@Override
	protected boolean containsFeature(String text, String feature) {
		return contains(text, feature);
	}

	/**
	 * the Pattern:
	 * <ul>
	 * <li>set flag DOTALL</li>
	 * <li>match any characters</li>
	 * <li>match any whitespace characters</li>
	 * <li>match "//# if/... [operators]feature[operators]"</li>
	 * <li>match any further characters</li>
	 * </ul>
	 */
	public static boolean contains(String text, String feature) {
		Pattern pattern = Pattern.compile(String.format(REGEX, feature));
		Matcher matcher = pattern.matcher(text);

		return matcher.find();
	}
}
