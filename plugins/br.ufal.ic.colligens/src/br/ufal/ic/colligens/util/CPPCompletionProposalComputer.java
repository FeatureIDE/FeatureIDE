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
import java.util.Collections;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.cdt.ui.text.contentassist.ContentAssistInvocationContext;
import org.eclipse.cdt.ui.text.contentassist.ICompletionProposalComputer;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.jdt.core.CompletionProposal;
import org.eclipse.jface.text.BadLocationException;
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

	private static final Image FEATURE_ICON = UIPlugin.getImage("FeatureIconSmall.ico");

	private Status status = Status.ShowNothing;

	List<CompletionProposal> directivesCompletionProposalList = Collections.emptyList();

	private IFile file;
	private IFeatureProject featureProject;

	private void init() {
		file = ((IFileEditorInput) PlatformUI.getWorkbench().getActiveWorkbenchWindow().getActivePage().getActiveEditor().getEditorInput()).getFile();
		featureProject = CorePlugin.getFeatureProject(file);
		status = Status.ShowNothing;
	}

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

	public List<CompletionProposal> getFeatureList(final IFeatureProject featureProject, final CharSequence prefix) {
		final Iterable<String> featureNames = FeatureUtils.getConcreteFeatureNames(featureProject.getFeatureModel());
		final LinkedList<CompletionProposal> completionProposalList = new LinkedList<CompletionProposal>();
		for (final String string : featureNames) {
			CompletionProposal proposal = null;
			proposal = CompletionProposal.create(CompletionProposal.LABEL_REF, prefix.length());
			proposal.setName(string.toCharArray());
			proposal.setCompletion(string.toCharArray());

			if (string.startsWith(prefix.toString())) {
				completionProposalList.add(proposal);
			}
		}

		final LinkedList<CompletionProposal> completionProposalsList = completionProposalList;
		return completionProposalsList;
	}

	@Override
	public List<ICompletionProposal> computeCompletionProposals(ContentAssistInvocationContext context, IProgressMonitor arg1) {

		if ((context == null) || (file == null) || (featureProject == null)) {
			return Collections.emptyList();
		}
		try {
			final int line = context.getDocument().getLineOfOffset(context.getInvocationOffset());
			final int offsetOfLine = context.getDocument().getLineOffset(line);
			final int lineLength = context.getDocument().getLineLength(line);
			final String lineContent = context.getDocument().get(offsetOfLine, lineLength);
			final String lastKeyword = findLastKeyword(lineContent);

			final boolean triggerAutocomplete = lineContent.trim() == "#";
			final boolean hasDirective = lineContainsElements(lineContent, CPPEnum.getAllDirectives());
			final boolean hasFeature = lineContainsElements(lineContent, (List<String>) FeatureUtils.getConcreteFeatureNames(featureProject.getFeatureModel()));
			final boolean newDirectives = (lastKeyword.contains("&&") || lastKeyword.contains("||"));

			if (triggerAutocomplete && !hasDirective) {
				status = Status.ShowDirectives;
			}
		}

		catch (final BadLocationException e1) {
			e1.printStackTrace();
		}

		if (status == Status.ShowNothing) {
			return Collections.emptyList();
		}

		CharSequence prefix = "";
		try {
			prefix = context.computeIdentifierPrefix();
		} catch (final BadLocationException e) {
			e.printStackTrace();
		}

		final CharSequence prefix1 = prefix;
		final LinkedList<CompletionProposal> completionProposalList1 = new LinkedList<CompletionProposal>();
		for (final String string : CPPEnum.getAllDirectives()) {
			CompletionProposal proposal1 = null;
			proposal1 = CompletionProposal.create(CompletionProposal.LABEL_REF, prefix1.length());
			proposal1.setName(string.toCharArray());
			proposal1.setCompletion(string.toCharArray());

			if (string.startsWith(prefix1.toString())) {
				completionProposalList1.add(proposal1);
			}
		}
		final LinkedList<CompletionProposal> completionProposalList = completionProposalList1;
		directivesCompletionProposalList = completionProposalList;

		final ArrayList<ICompletionProposal> list = new ArrayList<ICompletionProposal>();
		if (status == Status.ShowFeatures) {
			for (final CompletionProposal proposal : getFeatureList(featureProject, prefix)) {

				// final CompletionProposal completionProposal = new CompletionProposal(proposal, context);
				// completionProposal.setReplacementString(new String(proposal.getCompletion()).replace(prefix, ""));
				// completionProposal.setReplacementOffset(context.getInvocationOffset());
				// final CompletionProposal feature = completionProposal;
				// feature.setImage(FEATURE_ICON);

				// list.add(feature);
			}
		} else if (status == Status.ShowDirectives) {

			for (final CompletionProposal proposal : directivesCompletionProposalList) {

				// final CompletionProposal lazyJavaCompletionProposal = new CompletionProposal(proposal, context);
				// lazyJavaCompletionProposal.setReplacementString(new String(proposal.getCompletion()).replace(prefix, ""));
				// lazyJavaCompletionProposal.setReplacementOffset(context.getInvocationOffset());
				// final CompletionProposal syntax = lazyJavaCompletionProposal;

				// list.add(syntax);

			}
		}
		return list;
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

	private enum Status {
		ShowFeatures, ShowDirectives, ShowNothing
	}

}
