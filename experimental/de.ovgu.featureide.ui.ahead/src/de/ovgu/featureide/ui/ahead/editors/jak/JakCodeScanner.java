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
package de.ovgu.featureide.ui.ahead.editors.jak;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.jdt.ui.JavaUI;
import org.eclipse.jdt.ui.text.IColorManager;
import org.eclipse.jdt.ui.text.IJavaColorConstants;
import org.eclipse.jface.text.TextAttribute;
import org.eclipse.jface.text.rules.IRule;
import org.eclipse.jface.text.rules.IToken;
import org.eclipse.jface.text.rules.IWhitespaceDetector;
import org.eclipse.jface.text.rules.IWordDetector;
import org.eclipse.jface.text.rules.RuleBasedScanner;
import org.eclipse.jface.text.rules.SingleLineRule;
import org.eclipse.jface.text.rules.Token;
import org.eclipse.jface.text.rules.WhitespaceRule;
import org.eclipse.jface.text.rules.WordRule;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.graphics.RGB;

/**
 * A RuleBasedScanner that is used for syntax highlighting of Jak files.
 * 
 * @author Marcus Leich
 *
 */
public class JakCodeScanner extends RuleBasedScanner {
	
	private static String[] keywords= { "abstract", "break", "case", "catch", "class", "continue", "default", "do", "else", "extends", "final", "finally", "for", "if", "implements", "import", "instanceof", "interface", "native", "new", "package", "private", "protected", "public", "return", "static", "super", "switch", "synchronized", "this", "throw", "throws", "transient", "try", "volatile", "while" };
	private static String[] types= { "void", "boolean", "char", "byte", "short", "int", "long", "float", "double" };
	private static String[] constants= { "false", "null", "true" };
	private static String[] jak_keywords= { "layer", "refines", "Super()" };
	
	public JakCodeScanner () {
		
		IColorManager cm = JavaUI.getColorManager ();
		IToken string= new Token(new TextAttribute(cm.getColor(IJavaColorConstants.JAVA_STRING)));
		IToken keyword= new Token(new TextAttribute(cm.getColor(IJavaColorConstants.JAVA_KEYWORD)));
		Token type= new Token(new TextAttribute(cm.getColor(IJavaColorConstants.JAVA_KEYWORD)));
		IToken constant= new Token(new TextAttribute(cm.getColor(IJavaColorConstants.JAVA_KEYWORD)));
		Color color = cm.getColor(IJavaColorConstants.JAVA_KEYWORD);
		IToken jak_keyword= new Token(new TextAttribute(cm.getColor(new RGB(bright(color.getRed()), bright(color.getGreen()), bright(color.getBlue())))));

		List<IRule> rules= new ArrayList<IRule>();
		
		rules.add(new WhitespaceRule (new IWhitespaceDetector () {
			public boolean isWhitespace (char c) {
				return Character.isWhitespace(c);
			}
		}));
		
		// strings
		rules.add(new SingleLineRule("\"", "\"", string, (char) 0, true));
		rules.add(new SingleLineRule("'", "'", string, (char) 0, true));
			
		// keywords
		WordRule wordRule= new WordRule(new IWordDetector() {
			public boolean isWordStart(char c) {
				return Character.isJavaIdentifierStart(c);
			}
			public boolean isWordPart(char c) {
				return Character.isJavaIdentifierPart(c) || c == '(' || c == ')'; // braces added to support jak keyword "Super()"
			}
		});
				
		for (int i= 0; i < keywords.length; i++)
			wordRule.addWord(keywords[i], keyword);
		for (int i= 0; i < types.length; i++)
			wordRule.addWord(types[i], type);
		for (int i= 0; i < constants.length; i++)
			wordRule.addWord(constants[i], constant);
		for (int i= 0; i < jak_keywords.length; i++)
			wordRule.addWord(jak_keywords[i], jak_keyword);
		rules.add(wordRule); 
		
		
		IRule[] result= new IRule[rules.size()];
		rules.toArray(result);
		setRules(result);
	}

	private int bright(int color) {
		return Math.min(color + 96, 255);
	}

}
