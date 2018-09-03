/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2017  FeatureIDE team, University of Magdeburg, Germany
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
package br.ufal.ic.colligens.util;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.List;

import org.eclipse.cdt.ui.text.contentassist.ContentAssistInvocationContext;
import org.eclipse.cdt.ui.text.contentassist.ICompletionProposalComputer;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.contentassist.CompletionProposal;
import org.eclipse.jface.text.contentassist.ICompletionProposal;
import org.eclipse.jface.text.contentassist.IContextInformation;
import org.eclipse.swt.graphics.Image;
import org.eclipse.ui.IFileEditorInput;
import org.eclipse.ui.PlatformUI;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.ui.UIPlugin;

/**
 * Autocomplete computer for CPP preprocessor.
 *
 * @author Mohammed Khaled
 * @author Iris-Maria Banciu
 */
public class CPPCompletionProposalComputer implements ICompletionProposalComputer {

	private static final List<String> ALL_DIRECTIVES = CPPEnum.getAllDirectives();
	private static final Image FEATURE_ICON = UIPlugin.getImage("FeatureIconSmall.ico");

	ArrayList<ICompletionProposal> directivesCompletionProposalList;

	private IFile file;
	private Status status;
	private IFeatureProject featureProject;
	private boolean triggerAutocomplete;
	private boolean hasDirective;
	private boolean hasFeature;
	private boolean newDirectives;
	private boolean concatenationPossible;

	@Override
	public List<IContextInformation> computeContextInformation(ContentAssistInvocationContext arg0, IProgressMonitor arg1) {
		return Collections.emptyList();
	}

	@Override
	public String getErrorMessage() {
		return null;
	}

	@Override
	public void sessionEnded() {

	}

	@Override
	public void sessionStarted() {
		init();
	}

	@Override
	public List<ICompletionProposal> computeCompletionProposals(ContentAssistInvocationContext context, IProgressMonitor arg1) {

		if ((context == null) || (file == null) || (featureProject == null)) {
			return directivesCompletionProposalList;
		}

		computeCurrentStatus(context);

		if (status == Status.ShowNothing) {
			return directivesCompletionProposalList;
		}

		final CharSequence prefix = computePrefix(context);

		final ArrayList<String> featureNames = new ArrayList<String>(FeatureUtils.extractConcreteFeaturesAsStringList(featureProject.getFeatureModel()));
		directivesCompletionProposalList = new ArrayList<ICompletionProposal>();
		if (status == Status.ShowFeatures) {
			createListOfCompletionProposals(context, featureProject, prefix, featureNames, "");
		} else if (status == Status.ShowDirectives) {
			createListOfCompletionProposals(context, featureProject, prefix, ALL_DIRECTIVES, "#");
		}
		return directivesCompletionProposalList;
	}

	private void init() {
		file = ((IFileEditorInput) PlatformUI.getWorkbench().getActiveWorkbenchWindow().getActivePage().getActiveEditor().getEditorInput()).getFile();
		featureProject = CorePlugin.getFeatureProject(file);
		status = Status.ShowNothing;
	}

	private void createListOfCompletionProposals(ContentAssistInvocationContext context, final IFeatureProject featureProject, final CharSequence prefix,
			Collection<String> list, String stringPrefix) {

		for (final String string : list) {
			final int start = context.getInvocationOffset();
			final CompletionProposal proposal =
				new CompletionProposal(string, start, prefix.length(), string.length(), FEATURE_ICON, stringPrefix + string, null, null);

			if (string.startsWith(prefix.toString())) {
				directivesCompletionProposalList.add(proposal);
			}
		}
	}

	private CharSequence computePrefix(ContentAssistInvocationContext context) {
		CharSequence prefix = "";
		try {
			prefix = context.computeIdentifierPrefix();
		} catch (final BadLocationException e) {
			e.printStackTrace();
		}
		return prefix;
	}

	private void computeCurrentStatus(ContentAssistInvocationContext context) {
		try {
			final int line = context.getDocument().getLineOfOffset(context.getInvocationOffset());
			final int offsetOfLine = context.getDocument().getLineOffset(line);
			final int lineLength = context.getDocument().getLineLength(line);
			final String lineContent = context.getDocument().get(offsetOfLine, lineLength);
			final String lastKeywordOfLine = findLastKeyword(lineContent);
			final String firstKeywordOfLine = findFirstKeywordOfLine(lineContent);

			setSyntaxEnvironmentStatus(lineContent, firstKeywordOfLine, lastKeywordOfLine);
			setCurrentStatus();
		}

		catch (final BadLocationException e1) {
			e1.printStackTrace();
		}
	}

	private void setCurrentStatus() {
		if (triggerAutocomplete && !hasDirective) {
			status = Status.ShowDirectives;
		}
		if ((hasDirective && !hasFeature) || (concatenationPossible && newDirectives)) {
			status = Status.ShowFeatures;
		}
	}

	private void setSyntaxEnvironmentStatus(final String lineContent, final String firstKeyword, final String lastKeyword) {
		triggerAutocomplete = lineContent.trim().equals("#");
		hasDirective = lineContainsElements(lineContent, ALL_DIRECTIVES);
		hasFeature = lineContainsElements(lineContent, (List<String>) FeatureUtils.getConcreteFeatureNames(featureProject.getFeatureModel()));
		newDirectives = (lastKeyword.contains("&&") || lastKeyword.contains("||"));
		concatenationPossible = firstKeyword.equals("#" + CPPEnum.IF.getText());
	}

	private boolean lineContainsElements(String lineContent, List<String> list) {

		for (final String div : list) {
			if (lineContent.contains(div)) {
				return true;
			}
		}
		return false;
	}

	private String findLastKeyword(String context) {
		final String text = context.trim();
		final int indexofKeyword = text.lastIndexOf(" ");
		if (indexofKeyword < 0) {
			return text;
		}
		return text.substring(indexofKeyword).trim();
	}

	private String findFirstKeywordOfLine(String lineContent) {
		final String string[] = lineContent.split(" ", 2);
		return string[0];
	}

	private enum Status {
		ShowFeatures, ShowDirectives, ShowNothing
	}
}
