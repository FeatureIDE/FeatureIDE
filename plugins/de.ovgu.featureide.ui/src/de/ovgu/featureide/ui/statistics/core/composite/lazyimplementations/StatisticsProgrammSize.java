package de.ovgu.featureide.ui.statistics.core.composite.lazyimplementations;

import java.util.HashMap;

import de.ovgu.featureide.core.fstmodel.FSTClass;
import de.ovgu.featureide.core.fstmodel.FSTClassFragment;
import de.ovgu.featureide.core.fstmodel.FSTField;
import de.ovgu.featureide.core.fstmodel.FSTMethod;
import de.ovgu.featureide.core.fstmodel.FSTModel;
import de.ovgu.featureide.core.fstmodel.FSTRole;
import de.ovgu.featureide.ui.statistics.core.composite.LazyParent;
import de.ovgu.featureide.ui.statistics.core.composite.lazyimplementations.genericdatatypes.HashMapNode;

/**
 * TreeNode who stores the number of classes, roles, fields and methods of a
 * given {@link FSTModel}.<br>
 * This node should only be used for a feature oriented project.
 * 
 * @author Dominik Hamann
 * @author Patrick Haese
 */
public class StatisticsProgrammSize extends LazyParent {
	private FSTModel fstModel;

	/**
	 * Constructor for a {@code ProgrammSizeNode}.
	 * 
	 * @param description
	 *            description of the node shown in the view
	 * @param fstModel
	 *            FSTModel for the calculation
	 */
	public StatisticsProgrammSize(String description, FSTModel fstModel) {
		super(description);
		this.fstModel = fstModel;
	}

	@Override
	protected void initChildren() {
		HashMap<String, Integer> methodMap = new HashMap<String, Integer>();
		HashMap<String, Integer> fieldMap = new HashMap<String, Integer>();
		HashMap<String, Integer> classMap = new HashMap<String, Integer>();

		for (FSTClass class_ : fstModel.getClasses()) {
			for (FSTRole role : class_.getRoles()) {
				FSTClassFragment classFragment = role.getClassFragment();
				String packageName = classFragment.getPackage();
				String qualifiedPackageName = (packageName == null) ? "(default package)"
						: packageName;

				String roleName = classFragment.getName().endsWith(".java") ? classFragment
						.getName().substring(0, classFragment.getName().length() - 5)
						: classFragment.getName();
				String qualifiedRoleName = qualifiedPackageName + "."
						+ roleName;

				String qualifier = qualifiedRoleName + ".";


				
				for (FSTMethod method : classFragment.getMethods()) {
					String fullName = qualifier + method.getFullName();
					methodMap.put(fullName + "." + method.getFullName(),methodMap.containsKey(fullName) ? methodMap.get(fullName) + 1 : 1);
				}

				for (FSTField field : classFragment.getFields()) {
					String fullName = qualifier + field.getFullName();
					fieldMap.put(
							fullName,
							fieldMap.containsKey(fullName) ? fieldMap
									.get(fullName) + 1 : 1);
				}

				classMap.put(
						qualifiedRoleName,
						classMap.containsKey(qualifiedRoleName) ? classMap
								.get(qualifiedRoleName) + 1 : 1);
			}
		}
		
		addChild(new HashMapNode(NUMBER_CLASS + SEPARATOR
				+ classMap.keySet().size() + " | " + NUMBER_ROLE + SEPARATOR
				+ sum(classMap), null, classMap));
		addChild(new HashMapNode(NUMBER_FIELD_U + SEPARATOR
				+ fieldMap.keySet().size() + " | " + NUMBER_FIELD + SEPARATOR
				+ sum(fieldMap), null, fieldMap));
		addChild(new HashMapNode(NUMBER_METHOD_U + SEPARATOR
				+ methodMap.keySet().size() + " | " + NUMBER_METHOD + SEPARATOR
				+ sum(methodMap), null, methodMap));
	}

	private Integer sum(HashMap<String, Integer> input) {
		Integer sum = 0;
		for (Integer value : input.values()) {
			sum += value;
		}
		return sum;
	}
}