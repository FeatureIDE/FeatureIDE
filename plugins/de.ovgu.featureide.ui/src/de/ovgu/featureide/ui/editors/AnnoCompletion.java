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
package de.ovgu.featureide.ui.editors;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.jdt.core.CompletionProposal;
import org.eclipse.jdt.internal.ui.text.java.LazyJavaCompletionProposal;
import org.eclipse.jdt.ui.text.java.ContentAssistInvocationContext;
import org.eclipse.jdt.ui.text.java.IJavaCompletionProposalComputer;
import org.eclipse.jdt.ui.text.java.JavaContentAssistInvocationContext;
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
 * Context Completion
 *
 * @author Reimar Schr�ter
 * @author Marcus Pinnecke
 */
@SuppressWarnings("restriction")
public class AnnoCompletion implements IJavaCompletionProposalComputer {

	/**
	 *
	 */
	private static final Image FEATURE_ICON = UIPlugin.getImage("FeatureIconSmall.ico");
	private boolean newDirectives;

	private Preprocessor currentPreprocessor = Preprocessor.Unknown;
	private Status status = Status.ShowNothing;

	private IFile file;
	private IFeatureProject featureProject;

	public AnnoCompletion() {}

	private void setProjectDetails() {
		file = ((IFileEditorInput) PlatformUI.getWorkbench().getActiveWorkbenchWindow().getActivePage().getActiveEditor().getEditorInput()).getFile();
		featureProject = CorePlugin.getFeatureProject(file);
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
		setProjectDetails();
	}

	public List<CompletionProposal> getFeatureList(final IFeatureProject featureProject, final CharSequence prefix) {
		final Iterable<String> featureNames = FeatureUtils.getConcreteFeatureNames(featureProject.getFeatureModel());

		final LinkedList<CompletionProposal> completionProposalsList = createListOfCompletionProposals(prefix, featureNames);
		return completionProposalsList;
	}

	/**
	 * @param prefix
	 * @param list
	 * @return
	 */
	private LinkedList<CompletionProposal> createListOfCompletionProposals(final CharSequence prefix, final Iterable<String> list) {
		final LinkedList<CompletionProposal> completionProposalList = new LinkedList<CompletionProposal>();
		for (final String string : list) {
			CompletionProposal proposal = null;
			proposal = CompletionProposal.create(CompletionProposal.LABEL_REF, prefix.length());
			proposal.setName(string.toCharArray());
			proposal.setCompletion(string.toCharArray());

			if (string.startsWith(prefix.toString())) {
				completionProposalList.add(proposal);
			}
		}
		return completionProposalList;
	}

	public List<CompletionProposal> getAntennaCompletionProposals(final CharSequence prefix) {
		final LinkedList<CompletionProposal> completionProposalList = createListOfCompletionProposals(prefix, Directives.getAllDirectives());
		return completionProposalList;
	}

	@Override
	public List<ICompletionProposal> computeCompletionProposals(ContentAssistInvocationContext arg0, IProgressMonitor arg1) {

		currentPreprocessor = Preprocessor.getPreprocessor(featureProject);

		final JavaContentAssistInvocationContext context = setCurrentContext(arg0);

		if ((context == null) || (file == null) || (featureProject == null)) {
			return Collections.emptyList();
		}

		final Status contextValid = computeList(context);
		if (contextValid == Status.ShowNothing) {
			return Collections.emptyList();
		}

		CharSequence prefix = "";
		try {
			prefix = context.computeIdentifierPrefix();
		} catch (final BadLocationException e) {
			e.printStackTrace();
		}

		final List<CompletionProposal> completionProp = getFeatureList(featureProject, prefix);
		final List<CompletionProposal> completionDirectives = getAntennaCompletionProposals(prefix);

		final ArrayList<ICompletionProposal> list = new ArrayList<ICompletionProposal>();
		if (contextValid == Status.ShowFeatures) {
			for (final CompletionProposal prop : completionProp) {

				final LazyJavaCompletionProposal feature = new LazyJavaCompletionProposal(prop, context);
				feature.setImage(FEATURE_ICON);
				feature.setReplacementString(new String(prop.getCompletion()).replace(prefix, ""));
				feature.setReplacementOffset(context.getInvocationOffset());

				list.add(feature);
			}
		} else if (contextValid == Status.ShowDirectives) {

			for (final CompletionProposal prop : completionDirectives) {

				final LazyJavaCompletionProposal syntax = new LazyJavaCompletionProposal(prop, context);
				syntax.setReplacementString(new String(prop.getCompletion()).replace(prefix, ""));
				syntax.setReplacementOffset(context.getInvocationOffset());
				list.add(syntax);

			}
			return list;
		}
		return list;
	}

	/**
	 * @param arg0
	 * @return
	 */
	private JavaContentAssistInvocationContext setCurrentContext(ContentAssistInvocationContext arg0) {
		JavaContentAssistInvocationContext context = null;
		if (arg0 instanceof JavaContentAssistInvocationContext) {
			context = (JavaContentAssistInvocationContext) arg0;
		}
		return context;
	}

	private boolean hasElement(String lineContent, List<String> list) {

		for (final String div : list) {
			if (lineContent.contains(div)) {
				return true;
			}
		}
		return false;
	}

	/**
	 * @param context
	 * @author Mohammed Khaled
	 * @author Iris-Maria Banciu
	 */
	private String findLastKeyword(String context) {
		final String text = context.trim();
		final int indexofKeyword = text.lastIndexOf(" ");
		if (indexofKeyword < 0) {
			return text;
		}
		return text.substring(indexofKeyword).trim();
	}

	private Status computeList(JavaContentAssistInvocationContext context) {
		try {
			final int line = context.getDocument().getLineOfOffset(context.getInvocationOffset());
			final int offsetOfLine = context.getDocument().getLineOffset(line);
			final int lineLength = context.getDocument().getLineLength(line);
			final String lineContent = context.getDocument().get(offsetOfLine, lineLength);
			final String lastKeyword = findLastKeyword(lineContent);

			getStatusAccordingToPreprocessor(lineContent, lastKeyword);
		}

		catch (final BadLocationException e1) {
			e1.printStackTrace();
		}
		return status;
	}

	/**
	 * @param lineContent
	 * @param lastKeyword
	 */
	private void getStatusAccordingToPreprocessor(final String lineContent, final String lastKeyword) {
		switch (currentPreprocessor) {
		case Antenna:
			status = getStatusForAntenna(lineContent, lastKeyword);
		case Munge:
			status = getStatusForMunge(lineContent, lastKeyword);
		case C:
			status = getStatusForC(lineContent, lastKeyword);
		case Unknown:
			status = getStatusForAntenna(lineContent, lastKeyword);
		}
	}

	/**
	 * @param lineContent
	 * @param lastKeyword
	 * @return
	 */
	private Status getStatusForMunge(String lineContent, String lastKeyword) {
		// TODO Auto-generated method stub
		return null;
	}

	/**
	 * @param lineContent
	 * @param lastKeyword
	 * @return
	 */
	private Status getStatusForC(String lineContent, String lastKeyword) {
		// TODO Auto-generated method stub
		return null;
	}

	/**
	 * @param lineContent
	 * @param lastKeyword
	 * @return
	 */
	private Status getStatusForAntenna(final String lineContent, final String lastKeyword) {
		final boolean startsWithHashTag = lineContent.trim().substring(2).trim().contains("#");
		final boolean hasDirectives = hasElement(lineContent, Directives.getAllDirectives());
		final boolean showFeaturesAfterDirectives = hasElement(lineContent, Arrays.asList("#if", "#elif", "#condition"));
		final boolean hasFeatures = hasElement(lineContent, (List<String>) FeatureUtils.getConcreteFeatureNames(featureProject.getFeatureModel()));
		newDirectives = (lastKeyword.contains("&&") || lastKeyword.contains("||"));
		if ((startsWithHashTag && !hasDirectives)) {
			status = Status.ShowDirectives;
		} else {
			status = Status.ShowNothing;
		}
		if ((showFeaturesAfterDirectives && !hasFeatures) || (hasFeatures && hasDirectives && newDirectives)) {
			status = Status.ShowFeatures;
		}
		return status;
	}

	private enum Status {
		ShowFeatures, ShowDirectives, ShowNothing
	}

	private enum Preprocessor {
		Antenna, Munge, C, Unknown;

		public static Preprocessor getPreprocessor(final IFeatureProject featureProject) {
			switch (featureProject.getComposer().getName()) {
			case "Antenna":
				return Preprocessor.Antenna;
			case "Munge":
				return Preprocessor.Munge;
			case "C":
				return Preprocessor.C;
			default:
				return Preprocessor.Unknown;
			}
		}
	}
}
