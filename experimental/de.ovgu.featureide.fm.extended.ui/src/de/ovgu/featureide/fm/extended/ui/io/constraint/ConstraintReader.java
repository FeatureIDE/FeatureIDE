/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2016  FeatureIDE team, University of Magdeburg, Germany
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
 * See http://featureide.cs.ovgu.de/ for further information.
 */
package de.ovgu.featureide.fm.extended.ui.io.constraint;

import de.ovgu.featureide.fm.extended.ui.io.ReaderProblem;
import de.ovgu.featureide.fm.extended.ui.io.attribute.Attributes;

import java.io.BufferedReader;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.Set;
import java.util.StringTokenizer;

import org.antlr.runtime.ANTLRStringStream;
import org.antlr.runtime.CharStream;
import org.antlr.runtime.CommonTokenStream;
import org.antlr.runtime.RecognitionException;


public class ConstraintReader {
	
	public static final String PARSER_ERROR = "The syntax is not correct";
	
	private List<ReaderProblem> problems = new ArrayList<ReaderProblem>();
	
	private List<Equation> constraints = new ArrayList<Equation>();
	
	private Set<String> featureNames;
	
	private Attributes attributes;
	
	private ConstraintReader(Set<String> featureNames, Attributes attributes) {
		this.featureNames = featureNames;
		this.attributes = attributes;
	}
	
	private void readFile(String path) throws IOException {
		InputStream is = new FileInputStream(path);
		BufferedReader br = new BufferedReader(new InputStreamReader(is));
		String line;
		int i = 1;
		while ((line = br.readLine()) != null) {
			processLine(line, i++);
		}
		is.close();
	}
	
	private void readString(String string) {
		StringTokenizer st = new StringTokenizer(string, System.getProperty("line.separator"));
		int i = 1;
		while (st.hasMoreTokens()) {
			processLine(st.nextToken(), i++);
		}
	}
	
	private void processLine(String line, int no) {
		CharStream cs = new ANTLRStringStream(line);
		ConstraintLexer lexer = new ConstraintLexer(cs);
		CommonTokenStream tokens = new CommonTokenStream();
		tokens.setTokenSource(lexer);
		ConstraintParser parser = new ConstraintParser(tokens);
		
		String problemMessage = null;
		try {
			Equation eq = parser.constraint();
			
			if (lexer.hadError() || parser.hadError()) {
				problemMessage = PARSER_ERROR;
			} else {
				validate(eq, no);
			}
		} catch (RecognitionException e) {
			problemMessage = PARSER_ERROR;
		}
		
		// some error occurred, log it!
		if (problemMessage != null) {
			problems.add(new ReaderProblem(problemMessage, no));
		}
	}
	
	private void validate(Equation eq, int no) {
		String problemMessage = null;
		
		Iterator<WeightedTerm> it = eq.getWeightedTerms().iterator();
		while (problemMessage == null && it.hasNext()) {
			 Reference ref = it.next().getReference();
			 String feature = ref.getFeatureName();
			 ReferenceType type = ref.getType();
			 String attribute = ref.getAttributeName();
			 
			 if (!featureNames.contains(feature)) {
				 problemMessage = String.format("Feature %s does not exist", feature);
			 } else if (type == ReferenceType.ATTRIBUTE && !attributes.hasAttribute(feature, attribute)) {
				 problemMessage = String.format("Attribute %s.%s does not exist", feature, attribute);
			 }
		}
		
		if (problemMessage != null) {
			problems.add(new ReaderProblem(problemMessage, no));
		} else {
			constraints.add(eq); // everything worked fine, add constraint
		}
	}
			
	private List<ReaderProblem> getProblems() {
		return problems;
	}
	
	private List<Equation> getConstraints() {
		return constraints;
	}

	public static ConstraintReaderResult readFile(Set<String> featureNames, 
			Attributes attributes, String path) throws IOException {
		ConstraintReader reader = new ConstraintReader(featureNames, attributes);
		reader.readFile(path);
		return new ConstraintReaderResult(reader.getProblems(), reader.getConstraints());
	}
	
	public static ConstraintReaderResult readString(Set<String> featureNames, 
			Attributes attributes, String string) {
		ConstraintReader reader = new ConstraintReader(featureNames, attributes);
		reader.readString(string);
		return new ConstraintReaderResult(reader.getProblems(), reader.getConstraints());
	}
}
