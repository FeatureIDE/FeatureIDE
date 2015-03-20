package de.ovgu.featureide.ui.statistics.core.composite.lazyimplementations;

import java.util.HashMap;
import java.util.LinkedList;

import de.ovgu.featureide.core.fstmodel.FSTClass;
import de.ovgu.featureide.core.fstmodel.FSTInvariant;
import de.ovgu.featureide.core.fstmodel.FSTMethod;
import de.ovgu.featureide.core.fstmodel.FSTModel;
import de.ovgu.featureide.core.fstmodel.FSTRole;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.ui.statistics.core.composite.LazyParent;
import de.ovgu.featureide.ui.statistics.core.composite.Parent;
import de.ovgu.featureide.ui.statistics.core.composite.lazyimplementations.genericdatatypes.HashMapNode;

/**
 * Node for contract statistics.
 * 
 * @author Stefan Krueger
 * @author Florian Proksch
 */
public class StatisticsContractComplexityNew extends LazyParent {

	private final FSTModel fstModel;
	private final FeatureModel featModel;
	private final String contractComposition;

	public StatisticsContractComplexityNew(String description, FSTModel fstmodel, FeatureModel featmodel, String contractComposition) {
		super(description, null);
		this.fstModel = fstmodel;
		this.featModel = featmodel;
		this.contractComposition = contractComposition;
	}

	@Override
	protected void initChildren() {
		if (fstModel != null) {

			HashMap<String, Integer> classInvariantsMap = new HashMap<String, Integer>();
			HashMap<String, Integer> classMethodContractMap = new HashMap<String, Integer>();
			HashMap<String, Integer> classMethodMap = new HashMap<String, Integer>();
			HashMap<String, Integer> classMethodCountMap = new HashMap<String, Integer>();
			HashMap<String, Integer> contractRefinementMap = new HashMap<String, Integer>();
			HashMap<String, Integer> featureCountList = new HashMap<String, Integer>();

			int numInProject = 0, numInvariantsInProject = 0, numClassesWithContract = 0, numClassesWithInvariants = 0;
			for (FSTClass class_ : fstModel.getClasses()) {
				int numInClass = 0, numInvariantsInClass = 0;

				String packageName = (class_.getRoles().size() == 0) ? null : class_.getRoles().get(0).getClassFragment().getPackage();
				String fullClassName = ((packageName == null) ? "(default package)" : packageName) + "."
						+ ((class_.getName().endsWith(".java")) ? class_.getName().substring(0, class_.getName().length() - 5) : class_.getName());

				for (FSTRole role : class_.getRoles()) {
					for (@SuppressWarnings("unused")
					FSTInvariant invariant : role.getClassFragment().getInvariants()) {
						numInvariantsInClass++;
						featureCountList.put(role.getFeature().getName(),
								featureCountList.containsKey(role.getFeature().getName()) ? featureCountList.get(role.getFeature().getName()) + 1 : 1);
					}
					for (FSTMethod method : role.getClassFragment().getMethods()) {
						classMethodCountMap.put(fullClassName + "." + method.getFullName(), 1);
						if (method.hasContract()) {
							featureCountList.put(role.getFeature().getName(),
									featureCountList.containsKey(role.getFeature().getName()) ? featureCountList.get(role.getFeature().getName()) + 1 : 1);
							numInClass++;
							contractRefinementMap.put(method.getCompKey(),
									contractRefinementMap.containsKey(method.getCompKey()) ? (contractRefinementMap.get(method.getCompKey()) + 1) : 1);
							if (classMethodMap.get(fullClassName + "." + method.getFullName()) != null)
								classMethodMap.put(fullClassName + "." + method.getFullName(),
										classMethodMap.get(fullClassName + "." + method.getFullName()) + 1);
							else
								classMethodMap.put(fullClassName + "." + method.getFullName(), 1);
						}
					}
				}

				classMethodContractMap.put(fullClassName, numInClass);
				classInvariantsMap.put(fullClassName, numInvariantsInClass);

				numInvariantsInProject += numInvariantsInClass;
				numInProject += numInClass;
				numClassesWithContract += numInClass > 0 ? 1 : 0;
				numClassesWithInvariants += numInvariantsInClass > 0 ? 1 : 0;
			}

			HashMapNode methodsNode = new HashMapNode(NUMBER_METHOD_METHOD_CONTRACT + SEPARATOR + classMethodMap.keySet().size() + "/"
					+ classMethodCountMap.keySet().size() + " ("
					+ Math.round(100 * (classMethodMap.keySet().size() / (double) classMethodCountMap.keySet().size())) + "%)", null, classMethodMap);
			methodsNode.initChildren();
			for (Parent p : methodsNode.getChildren()) {
				LinkedList<String> featureChildList = new LinkedList<String>();

				for (FSTClass class_ : fstModel.getClasses()) {

					String packageName = (class_.getRoles().size() == 0) ? null : class_.getRoles().get(0).getClassFragment().getPackage();
					String fullClassName = ((packageName == null) ? "(default package)" : packageName) + "."
							+ ((class_.getName().endsWith(".java")) ? class_.getName().substring(0, class_.getName().length() - 5) : class_.getName());

					for (FSTRole role : class_.getRoles()) {

						for (FSTMethod method : role.getClassFragment().getMethods()) {
							if (method.hasContract()) {

								if (p.getDescription().equals(fullClassName + "." + method.getFullName())) {
									featureChildList.add(role.getFeature().getName());

								}
							}
						}
					}
				}

				LinkedList<String> featureOrderList = new LinkedList<String>(featModel.getFeatureOrderList());
				featureOrderList.retainAll(featureChildList);
				for (String s : featureOrderList) {
					p.addChild(new Parent(s));
				}
			}

			addChild(new SumImplementationArtifactsParent(NUMBER_PROJECT_INVARIANT + SEPARATOR + numInvariantsInProject + " | " + NUMBER_CLASS_INVARIANT
					+ SEPARATOR + numClassesWithInvariants + "/" + fstModel.getClasses().size() + " ("
					+ Math.round(100 * (numClassesWithInvariants / (double) fstModel.getClasses().size())) + "%)", fstModel, 3));
			addChild(new SumImplementationArtifactsParent(NUMBER_PROJECT_METHOD_CONTRACT + SEPARATOR + numInProject + " | " + NUMBER_CLASS_METHOD_CONTRACT
					+ SEPARATOR + numClassesWithContract + "/" + fstModel.getClasses().size() + " ("
					+ Math.round(100 * (numClassesWithContract / (double) fstModel.getClasses().size())) + "%)", fstModel, 4));
			addChild(new SumImplementationArtifactsParent(NUMBER_METHOD_METHOD_CONTRACT + SEPARATOR + classMethodMap.keySet().size() + "/"
					+ classMethodCountMap.keySet().size() + " ("
					+ Math.round(100 * (classMethodMap.keySet().size() / (double) classMethodCountMap.keySet().size())) + "%)", fstModel, 5));

			HashMap<String, Integer> contractRefinementRealNameMap = new HashMap<String, Integer>();
			if (contractComposition.equals("Method-based Composition")) {
				for (String refinement : contractRefinementMap.keySet()) {
					contractRefinementRealNameMap.put(REFINEMENT_COMPOSING_MECHANISM_MAPPING.get(refinement.trim()), contractRefinementMap.get(refinement));
				}
			} else {
				for (String refinement : contractRefinementMap.keySet()) {
					contractRefinementRealNameMap.put(
							"Project based - " + contractComposition,
							contractRefinementMap.get(refinement)
									+ (contractRefinementRealNameMap.containsKey("Project based - " + contractComposition) ? contractRefinementRealNameMap
											.get("Project based - " + contractComposition) : 0));
				}
			}
			//TODO new node?
			addChild(new HashMapNode(METHOD_CONTRACT_REFINEMENT, null, contractRefinementRealNameMap));

			addChild(new SumImplementationArtifactsParent(METHOD_CONTRACTS_FEATURE, fstModel, 6));

		}
	}
}
