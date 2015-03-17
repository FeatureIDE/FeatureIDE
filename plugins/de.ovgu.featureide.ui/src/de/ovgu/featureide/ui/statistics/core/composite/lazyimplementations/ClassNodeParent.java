package de.ovgu.featureide.ui.statistics.core.composite.lazyimplementations;

import java.util.LinkedList;

import de.ovgu.featureide.core.fstmodel.FSTClass;
import de.ovgu.featureide.core.fstmodel.FSTClassFragment;
import de.ovgu.featureide.core.fstmodel.FSTModel;
import de.ovgu.featureide.core.fstmodel.FSTRole;
import de.ovgu.featureide.ui.statistics.core.composite.Parent;
import de.ovgu.featureide.ui.statistics.core.composite.lazyimplementations.genericdatatypes.AbstractSortModeNode;

/**
 * Node to display the methods in the StatisticsProgrammSize
 * 
 * @author Schleicher Miro
 */
public class ClassNodeParent extends AbstractSortModeNode {

	private final FSTModel fstModel;

	private FSTClass fstClass;
	private FSTClassFragment fstClassFrag;

	public ClassNodeParent(String descString, FSTClass fstClass, FSTModel fstMod) {
		super(descString, fstClass.getRoles().size());
		this.fstClass = fstClass;
		this.fstModel = fstMod;

	}

	public ClassNodeParent(String descString, FSTClassFragment fstClassFrag, FSTModel fstMod) {
		super(descString);
		this.fstClassFrag = fstClassFrag;
		this.fstModel = fstMod;
	}

	@Override
	protected void initChildren() {
		if (fstClass != null) {
			for (FSTRole fstRole : fstClass.getRoles()) {
				addChild(new Parent(fstRole.getFeature().getName(), fstRole));
			}
		} else if (fstClassFrag != null) {

			for (FSTClass currClass : fstModel.getClasses()) {
				for (LinkedList<FSTClassFragment> classFragmentList : currClass.getAllFSTFragments()) {
					for (FSTClassFragment fstFrag : classFragmentList) {
						if (fstFrag.getFullIdentifier().equals(fstClassFrag.getFullIdentifier())) {
							addChild(new ClassSubNodeParent(fstFrag.getRole().getFeature().getName(), fstFrag));
						}
					}
				}
			}
		}
	}

}
