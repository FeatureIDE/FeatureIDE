/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2009  FeatureIDE Team, University of Magdeburg
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
package de.ovgu.featureide.ui.ahead.editors.jak;

import java.text.MessageFormat;
import java.util.ArrayList;
import java.util.List;

import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.ITextViewer;
import org.eclipse.jface.text.TextPresentation;
import org.eclipse.jface.text.contentassist.CompletionProposal;
import org.eclipse.jface.text.contentassist.ContextInformation;
import org.eclipse.jface.text.contentassist.ICompletionProposal;
import org.eclipse.jface.text.contentassist.IContentAssistProcessor;
import org.eclipse.jface.text.contentassist.IContextInformation;
import org.eclipse.jface.text.contentassist.IContextInformationPresenter;
import org.eclipse.jface.text.contentassist.IContextInformationValidator;



/**
 * This class computes the proposals for the auto completion / content assistant.
 * 
 * @author Constanze Adler
 */
public class JakCompletionProcessor implements IContentAssistProcessor {
	public static final String ID = "featureide.ui.ahead.editors.jak.JakCompletionProcessor";
	protected static class Validator implements IContextInformationValidator, IContextInformationPresenter {

		protected int fInstallOffset;
		
		@Override
		public void install(IContextInformation info, ITextViewer viewer,
				int offset) {
			fInstallOffset= offset;
		}

		@Override
		public boolean isContextInformationValid(int offset) {
			return Math.abs(fInstallOffset - offset) < 5;
		}

		@Override
		public boolean updatePresentation(int offset,
				TextPresentation presentation) {
			return false;
		}
		
	}
	
	protected final static String[] fgProposals=
	{"Super()","refines", "layer","abstract", "boolean", "break", "byte", "case", "catch", "char", "class", "continue", "default", "do", "double", "else", "extends", "false", "final", "finally", "float", "for", "if", "implements", "import", "instanceof", "int", "interface", "long", "native", "new", "null", "package", "private", "protected", "public", "return", "short", "static", "super", "switch", "synchronized", "this", "throw", "throws", "transient", "true", "try", "void", "volatile", "while" }; //$NON-NLS-48$ //$NON-NLS-47$ //$NON-NLS-46$ //$NON-NLS-45$ //$NON-NLS-44$ //$NON-NLS-43$ //$NON-NLS-42$ //$NON-NLS-41$ //$NON-NLS-40$ //$NON-NLS-39$ //$NON-NLS-38$ //$NON-NLS-37$ //$NON-NLS-36$ //$NON-NLS-35$ //$NON-NLS-34$ //$NON-NLS-33$ //$NON-NLS-32$ //$NON-NLS-31$ //$NON-NLS-30$ //$NON-NLS-29$ //$NON-NLS-28$ //$NON-NLS-27$ //$NON-NLS-26$ //$NON-NLS-25$ //$NON-NLS-24$ //$NON-NLS-23$ //$NON-NLS-22$ //$NON-NLS-21$ //$NON-NLS-20$ //$NON-NLS-19$ //$NON-NLS-18$ //$NON-NLS-17$ //$NON-NLS-16$ //$NON-NLS-15$ //$NON-NLS-14$ //$NON-NLS-13$ //$NON-NLS-12$ //$NON-NLS-11$ //$NON-NLS-10$ //$NON-NLS-9$ //$NON-NLS-8$ //$NON-NLS-7$ //$NON-NLS-6$ //$NON-NLS-5$ //$NON-NLS-4$ //$NON-NLS-3$ //$NON-NLS-2$ //$NON-NLS-1$

	protected IContextInformationValidator fValidator= new Validator();
	
	public JakCompletionProcessor(){
		super();
	}

	/* (non-Javadoc)
	 * @see org.eclipse.jface.text.contentassist.IContentAssistProcessor#computeCompletionProposals(org.eclipse.jface.text.ITextViewer, int)
	 */
	@Override
	public ICompletionProposal[] computeCompletionProposals(ITextViewer viewer,
			int offset) {
		List<CompletionProposal> propList = new ArrayList<CompletionProposal>();
		computeProposals(propList, viewer,offset);
		if (propList==null) return null;
		ICompletionProposal[] result= new ICompletionProposal[propList.size()];
		propList.toArray(result);
	/*	ICompletionProposal[] result= new ICompletionProposal[fgProposals.length];
		for (int i= 0; i < fgProposals.length; i++) {
			IContextInformation info= new ContextInformation(fgProposals[i], MessageFormat.format(JakEditorMessages.getString("CompletionProcessor.Proposal.ContextInfo.pattern"), new Object[] { fgProposals[i] })); //$NON-NLS-1$
			result[i]= new CompletionProposal(fgProposals[i], offset, 0, fgProposals[i].length(), null, fgProposals[i], info, MessageFormat.format(JakEditorMessages.getString("CompletionProcessor.Proposal.hoverinfo.pattern"), new Object[] { fgProposals[i]})); //$NON-NLS-1$
		}*/
		return result;
	}

	/* (non-Javadoc)
	 * @see org.eclipse.jface.text.contentassist.IContentAssistProcessor#computeContextInformation(org.eclipse.jface.text.ITextViewer, int)
	 */
	@Override
	public IContextInformation[] computeContextInformation(ITextViewer viewer,
			int offset) {
		IContextInformation[] result= new IContextInformation[5];
		for (int i= 0; i < result.length; i++)
			result[i]= new ContextInformation(
					MessageFormat.format(JakEditorMessages.getString("CompletionProcessor.ContextInfo.display.pattern"), new Object[] { new Integer(i), new Integer(offset) }),  //$NON-NLS-1$
					MessageFormat.format(JakEditorMessages.getString("CompletionProcessor.ContextInfo.value.pattern"), new Object[] { new Integer(i), new Integer(offset - 5), new Integer(offset + 5)})); //$NON-NLS-1$
		return result;
	}

	/* (non-Javadoc)
	 * @see org.eclipse.jface.text.contentassist.IContentAssistProcessor#getCompletionProposalAutoActivationCharacters()
	 */
	@Override
	public char[] getCompletionProposalAutoActivationCharacters() {
		return new char[] { '.', '(' };
	}

	/* (non-Javadoc)
	 * @see org.eclipse.jface.text.contentassist.IContentAssistProcessor#getContextInformationAutoActivationCharacters()
	 */
	@Override
	public char[] getContextInformationAutoActivationCharacters() {
		return new char[] { '#' };
	}

	/* (non-Javadoc)
	 * @see org.eclipse.jface.text.contentassist.IContentAssistProcessor#getContextInformationValidator()
	 */
	@Override
	public IContextInformationValidator getContextInformationValidator() {
		return fValidator;
	}

	/* (non-Javadoc)
	 * @see org.eclipse.jface.text.contentassist.IContentAssistProcessor#getErrorMessage()
	 */
	@Override
	public String getErrorMessage() {
		// TODO Auto-generated method stub
		return null;
	}
	private void computeProposals(List<CompletionProposal> propList, ITextViewer viewer, int offset)
	{
		//retrieve current document
		IDocument doc = viewer.getDocument();
		
		try {
			int line = doc.getLineOfOffset(offset);
			int length = doc.getLineLength(line);
			String text = doc.get(offset-(length-1),length);
			System.out.println(text);
			String help = text.trim();
			if (help.equals(".")){
				propList = null;
				return;
			}
		} catch (BadLocationException e) {
			System.out.println(e.getMessage());
		}
		
		for (int i= 0; i < fgProposals.length; i++) {
			IContextInformation info= new ContextInformation(fgProposals[i], MessageFormat.format(JakEditorMessages.getString("CompletionProcessor.Proposal.ContextInfo.pattern"), new Object[] { fgProposals[i] })); //$NON-NLS-1$
			propList.add(new CompletionProposal(fgProposals[i], offset, 0, fgProposals[i].length(), null, fgProposals[i], info, MessageFormat.format(JakEditorMessages.getString("CompletionProcessor.Proposal.hoverinfo.pattern"), new Object[] { fgProposals[i]}))); //$NON-NLS-1$
		}
		
	/*	String FeatureIDE = "FeatureIDE";
		IContextInformation info= new ContextInformation(FeatureIDE, MessageFormat.format(JakEditorMessages.getString("CompletionProcessor.Proposal.ContextInfo.pattern"), new Object[] { FeatureIDE })); //$NON-NLS-1$
		propList.add(new CompletionProposal(FeatureIDE, offset, 0, FeatureIDE.length(), null, FeatureIDE, info, MessageFormat.format(JakEditorMessages.getString("CompletionProcessor.Proposal.hoverinfo.pattern"), new Object[] { FeatureIDE})));
	   */
	}
}
