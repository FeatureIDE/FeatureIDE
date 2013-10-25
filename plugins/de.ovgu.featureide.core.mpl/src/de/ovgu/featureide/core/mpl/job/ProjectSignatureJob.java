package de.ovgu.featureide.core.mpl.job;

import de.ovgu.featureide.core.mpl.signature.ProjectSignatures.SignatureIterator;
import de.ovgu.featureide.core.mpl.signature.ProjectStructure;
import de.ovgu.featureide.core.mpl.signature.filter.ISignatureFilter;
import de.ovgu.featureide.core.mpl.signature.fuji.FujiClassCreator;

public class ProjectSignatureJob extends AChainJob {
	private final ISignatureFilter filter;
	private final ProjectStructure projectSig;

	public ProjectSignatureJob(ProjectStructure projectSig, ISignatureFilter filter) {
		super("Loading Project Signature");
		this.filter = filter;
		this.projectSig = projectSig;
	}
	
	@Override
	protected boolean work() {
		SignatureIterator it = interfaceProject.getProjectSignatures().createIterator();
		it.addFilter(filter);
		projectSig.construct(it, new FujiClassCreator());
		return true;
	}
}
