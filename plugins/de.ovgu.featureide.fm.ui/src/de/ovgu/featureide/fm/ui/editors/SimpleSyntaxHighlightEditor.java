/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2013  FeatureIDE team, University of Magdeburg, Germany
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
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.fm.ui.editors;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Locale;
import java.util.Set;
import java.util.regex.MatchResult;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jface.resource.FontRegistry;
import org.eclipse.jface.resource.JFaceResources;
import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.StyleRange;
import org.eclipse.swt.custom.StyledText;
import org.eclipse.swt.events.ModifyEvent;
import org.eclipse.swt.events.ModifyListener;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.graphics.Font;
import org.eclipse.swt.layout.FillLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.progress.UIJob;

/**
 * Simple syntax highlighted editor
 * 
 * @author Marcus Pinnecke
 */
public class SimpleSyntaxHighlightEditor extends StyledText {

	private String[] keywords;
	private Set<String> possibleWords = new HashSet<String>();
	private Set<String> unknownWords = new HashSet<String>();

	/**
	 * @param parent
	 * @param style
	 */
	public SimpleSyntaxHighlightEditor(Composite parent, int style, final String[] keywords) {
		super(parent, style);
		this.keywords = keywords;

		this.keywordColor = Display.getDefault().getSystemColor(SWT.COLOR_DARK_RED);
		this.wrongWordColor = Display.getDefault().getSystemColor(SWT.COLOR_RED);
		this.normalColor = Display.getDefault().getSystemColor(SWT.COLOR_BLACK);
		this.setFont(JFaceResources.getTextFont());
		
		super.addModifyListener(new ModifyListener() {

			@Override
			public void modifyText(ModifyEvent e) {
				updateHighlight();
			}
		});
	}

	private Color keywordColor;
	private Color wrongWordColor;
	private Color normalColor;
	private boolean underlineEverything;
	
	public Set<String> getUnknownWords() 
	{
		return unknownWords;
	}
	
	public void setPossibleWords(Set<String> words) {
		possibleWords.clear();
		possibleWords.addAll(words);
		for (int i = 0; i <keywords.length; i++)
			possibleWords.add(keywords[i].toLowerCase());
	}

	private void updateHighlight() {
		if (!underlineEverything) {
			final String text = super.getText();
			
			StyleRange resetStyleRange = new StyleRange();
			resetStyleRange.start = 0;
			resetStyleRange.length = text.length();
			resetStyleRange.fontStyle = SWT.NORMAL;
			resetStyleRange.foreground = normalColor;
			setStyleRange(resetStyleRange);
	
			hightlightKeywords(text);
			hightlightWrongWords(text);
		}
	}
	
	/**
	 * @param text
	 */
	private void hightlightWrongWords(String text) {
		
		unknownWords.clear();
		
		for (int i = 0; i < keywords.length; i++)
			possibleWords.add(keywords[i]);
		
		String safeCopy = new String(text);
		safeCopy = safeCopy.replace("(", " ").replace(")", " ");
		
		System.out.println("---------------------\n" + safeCopy);
		
		String[] tokens = safeCopy.split(" ");
		int start = 0;
		for (int i = 0; i< tokens.length; i++) {
			String token = tokens[i].trim();
			System.out.println("token " + token);
			
			if (!token.isEmpty() && !possibleWords.contains(token) && !possibleWords.contains(token.toLowerCase())) {
				unknownWords.add(token);
				
				StyleRange styleRange = new StyleRange();
				styleRange.start = start;
				styleRange.length = token.length();
				styleRange.underlineStyle = SWT.UNDERLINE_ERROR;
				styleRange.underline = true;
				styleRange.underlineColor = wrongWordColor;
				styleRange.foreground = normalColor;

				setStyleRange(styleRange);				
			}
			start += tokens[i].length() + 1;
		}
	}

	/**
	 * 
	 */
	private void hightlightKeywords(String text) {
		final List<MatchResult> keywordPositions = new ArrayList<MatchResult>();

		for (int i = 0; i < keywords.length; i++) {
			final String regex = keywords[i].equals("(") ? "\\(" : keywords[i].equals(")") ? "\\)" : " " + keywords[i].toLowerCase() + " "; 
			keywordPositions.addAll(findMatchingPositions(Pattern.compile(regex), text));
		}

		// highlight keywords at the beginning
		for (int j = 0; j < keywords.length; j++) {
			if (this.getText().toLowerCase().startsWith(keywords[j].toLowerCase())) {
				
				StyleRange styleRange = new StyleRange();
				styleRange.start = 0;
				styleRange.length = keywords[j].length();
				styleRange.fontStyle = SWT.BOLD;
				styleRange.foreground = keywordColor;

				setStyleRange(styleRange);				
				break;
			}
		}
		
		// highlight keywords in text
		for (int j = 0; j < keywordPositions.size(); j++) {

			StyleRange styleRange = new StyleRange();
			styleRange.start = keywordPositions.get(j).start();
			styleRange.length = keywordPositions.get(j).end() - keywordPositions.get(j).start();
			styleRange.fontStyle = SWT.BOLD;
			styleRange.foreground = keywordColor;

			setStyleRange(styleRange);
		}
	}

	public void copyIn(final String textToInsert) {
		StringBuilder temp = new StringBuilder(super.getText());
		
		int selStart = super.getSelectionRanges()[0];
		int selLen = super.getSelectionRanges()[1];
		
		if (selLen != 0) {
			temp.delete(selStart, selStart + selLen);
		}
		
		String prefix = "";
		if (selStart - 1 > 0)
			prefix += temp.charAt(selStart - 1) == ' ' ? "" : " ";
		String suffix = "";
		int lastIndex = selStart + prefix.length() + textToInsert.length();
		suffix += lastIndex >= temp.length() ? " " : (temp.charAt(lastIndex) == ' ' ? "" : " ");
		
		temp.insert(selStart, prefix + textToInsert + suffix);
		super.setText(temp.toString());
		super.setFocus();
		super.setSelection(selStart + prefix.length() + textToInsert.length() + suffix.length());
	}

	private List<MatchResult> findMatchingPositions(Pattern pattern, String text) {
		final Matcher matcher = pattern.matcher(text);
		List<MatchResult> retval = new ArrayList<MatchResult>();
		while (matcher.find())
			retval.add(matcher.toMatchResult());
		return retval;
	}

	/**
	 * 
	 */
	public void UnderlineEverything(boolean b) {
		underlineEverything = b;
		if (underlineEverything) {
			StyleRange styleRange = new StyleRange();
			styleRange.start = 0;
			styleRange.length = this.getText().length();
			styleRange.fontStyle = SWT.NORMAL;
			styleRange.foreground = normalColor;
			styleRange.underlineStyle = SWT.UNDERLINE_ERROR;
			styleRange.underline = true;
			styleRange.underlineColor = wrongWordColor;
			setStyleRange(styleRange);
		} else updateHighlight();
	}

}
