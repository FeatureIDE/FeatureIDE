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
package de.ovgu.featureide.munge.model;

import java.util.Iterator;
import java.util.LinkedList;
import java.util.Stack;
import java.util.Vector;
import java.util.regex.Matcher;

import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.fstmodel.preprocessor.FSTDirective;
import de.ovgu.featureide.core.fstmodel.preprocessor.PPModelBuilder;
import de.ovgu.featureide.munge.MungePreprocessor;

/**
 * Build the FSTModel for munge projects.
 * 
 * @author Jens Meinicke
 * @author Sebastian Krieter
 */
public class MungeModelBuilder extends PPModelBuilder{

	public MungeModelBuilder(IFeatureProject featureProject) {
		super(featureProject);
	}

	@Override
	protected boolean containsFeature(String text, String feature) {
		return text.contains("end[" + feature + "]");
	}
	
	@Override
	public LinkedList<FSTDirective> buildModelDirectivesForFile(Vector<String> lines) {
		//for preprocessor outline
		Stack<FSTDirective> directivesStack = new Stack<FSTDirective>();
		LinkedList<FSTDirective> directivesList = new LinkedList<FSTDirective>();
		
		boolean commentSection = false;
		
		Iterator<String> linesIt = lines.iterator();
		int lineCount = 0;
		int id = 0;
		
		while (linesIt.hasNext()) {
			String line = linesIt.next();
			
			// if line is preprocessor directive
			if (line.contains(MungePreprocessor.COMMENT_START) || 
					line.contains(MungePreprocessor.COMMENT_END) || 
					commentSection) {
				Matcher m = MungePreprocessor.OP_COM_PATTERN.matcher(line);
				
				while (m.find()) {
					String completeElement = m.group(0);
					String singleElement = m.group(2);
					String expression = m.group(4);
					
					if (singleElement == null) {
						if (completeElement.equals(MungePreprocessor.COMMENT_START)) {
							commentSection = true;
						} else if (completeElement.equals(MungePreprocessor.COMMENT_END)) {
							commentSection = false;
						}
					} else {
						FSTDirective directive = new FSTDirective(id++);
						
						int command = 0;
						
						if (singleElement.equals("if")) {
							command = FSTDirective.IF;
						} else if (singleElement.equals("if_not")) {
							command = FSTDirective.IF;
						} else if (singleElement.equals("else")) {
							command = FSTDirective.ELSE;
							directivesStack.pop();
						} else if (singleElement.equals("end")) {
							directivesStack.pop().setEndLine(lineCount, m.end(0)+MungePreprocessor.COMMENT_END.length());
							continue;
						} else {
							continue;
						}
						
						directive.setCommand(command);
						directive.setExpression(expression != null ? expression : "");				
						directive.setStartLine(lineCount, m.start(0)-MungePreprocessor.COMMENT_START.length());
						
						if(!directivesStack.isEmpty()){
							FSTDirective top = directivesStack.peek();
							top.addChild(directive);
						} else {
							directivesList.add(directive);
						}
						
						directivesStack.push(directive);
					}
				}
			}
			lineCount++;
		}
		return directivesList;
	}
}
