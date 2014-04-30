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
package de.ovgu.featureide.core.mpl.signature;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Map;
import java.util.Map.Entry;

import de.ovgu.featureide.core.mpl.signature.ProjectSignatures.SignatureIterator;
import de.ovgu.featureide.core.mpl.signature.abstr.AClassCreator;
import de.ovgu.featureide.core.mpl.signature.abstr.AbstractClassFragment;
import de.ovgu.featureide.core.mpl.signature.abstr.AbstractClassSignature;
import de.ovgu.featureide.core.mpl.signature.abstr.AbstractFieldSignature;
import de.ovgu.featureide.core.mpl.signature.abstr.AbstractMethodSignature;
import de.ovgu.featureide.core.mpl.signature.abstr.AbstractSignature;
import de.ovgu.featureide.core.mpl.signature.fuji.FujiClassCreator;

/** 
 * Representation of {@link ProjectSignatures} as a list of classes.
 * 
 * @author Sebastian Krieter
 */
public class ProjectStructure {

	protected final HashMap<String, AbstractClassFragment> classList = new HashMap<String, AbstractClassFragment>();
	
	protected int hashCode = 0;
	protected boolean hasHashCode = false;
	
	public ProjectStructure(SignatureIterator it) {
		construct(it, new FujiClassCreator());
	}
	
	public void construct(SignatureIterator allMembers, AClassCreator aClassCreator) {
		classList.clear();
		LinkedList<AbstractClassSignature> parents = new LinkedList<AbstractClassSignature>();
		allMembers.reset();
		while (allMembers.hasNext()) {
			AbstractSignature sig = allMembers.next();
			AbstractClassSignature parent = sig.getParent();
			parents.clear();
			final boolean isMember;
			if (sig instanceof AbstractClassSignature) {
				parents.addFirst((AbstractClassSignature) sig);
				isMember = false;
			} else {
				isMember = true;
			}
			while (parent != null) {
				parents.addFirst(parent);
				parent = parent.getParent();
			}
			
			parent = parents.removeFirst();
			AbstractClassFragment parentClass = getClass(parent.getFullName());
			if (parentClass == null) {
				parentClass = aClassCreator.create(parent);
				addClass(parentClass);
			} else {
				if (sig instanceof AbstractClassSignature) {
					AbstractClassSignature parentSig = parentClass.getSignature();
					for (String newImport : ((AbstractClassSignature)sig).getImportList()) {
						parentSig.addImport(newImport);
					}
				}
			}
			
			for (AbstractClassSignature child : parents) {
				AbstractClassFragment childClass = parentClass.getInnerClass(child.getFullName());
				
				if (childClass == null) {
					childClass = aClassCreator.create(child);
					parentClass.addInnerClass(childClass);
				}
				parentClass = childClass;
			}
			if (isMember) {
				parentClass.addMember(sig);
			}
		}
	}

	public AbstractClassFragment getClass(String id) {
		return classList.get(id);
	}
	
	public Collection<AbstractClassFragment> getClasses() {
		return classList.values();
	}
	
	private void addClass(AbstractClassFragment classSig) {
		classList.put(classSig.getSignature().getFullName(), classSig);
	}

	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		
		ProjectStructure otherSig = (ProjectStructure) obj;
		
		if (otherSig == null 
				|| classList.size() != otherSig.classList.size()) {
			return false;
		}
		for (Entry<String, AbstractClassFragment> entrySet : classList.entrySet()) {
			AbstractClassFragment otherClassSig = otherSig.classList.get(entrySet.getKey());
			if (otherClassSig == null || !otherClassSig.equals(entrySet.getValue())) {
				return false;
			}
		}
		return true;
	}

	@Override
	public int hashCode() {
		if (!hasHashCode) {
			hashCode = 1;
			for (AbstractClassFragment cls : classList.values()) {
				hashCode = hashCode + cls.hashCode();
			}
			hasHashCode = true;
		}
		return hashCode;
	}

	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder();
		for (AbstractClassFragment cls : classList.values()) {
			sb.append(cls.toString());
		}
		return sb.toString();
	}
	
	public double similarityTo(ProjectStructure otherSig) {
		int[] countedMembers = countEqMembers(classList, otherSig.classList);
		double eqMemberCount = countedMembers[0];
		double memberCount = countedMembers[1];
		
		final int rf = 1000;

		return (memberCount == 0) ? 1 : Math.floor(rf * eqMemberCount / memberCount) / rf;
	}
	
	private int[] countEqMembers(Map<String, AbstractClassFragment> thisClassSigMap, Map<String, AbstractClassFragment> otherClassSigMap) {		
		int memberCount = 0, eqMemberCount = 0;
		
		if (!thisClassSigMap.isEmpty() && !otherClassSigMap.isEmpty()) {
			final HashSet<String> ids = new HashSet<String>(thisClassSigMap.keySet());
			ids.addAll(otherClassSigMap.keySet());
			memberCount += ids.size();
			
			for (String id : ids) {
				final AbstractClassFragment 
					thisClassSig = thisClassSigMap.get(id),
					otherClassSig = otherClassSigMap.get(id);
				if (thisClassSig == null) {
					memberCount += otherClassSig.getMemberCount();
				} else if (otherClassSig == null) {
					memberCount += thisClassSig.getMemberCount();
				} else {
					eqMemberCount++;
					
					final HashSet<AbstractSignature> members = new HashSet<AbstractSignature>(thisClassSig.getMembers());
					memberCount += members.size();
					
					for (AbstractSignature otherMember : otherClassSig.getMembers()) {
						if (members.add(otherMember)) {
							memberCount++;
						} else {
							eqMemberCount++;
						}
					}
					
					int[] countedMembers = countEqMembers(thisClassSig.getInnerClasses(), otherClassSig.getInnerClasses());
					eqMemberCount += countedMembers[0];
					memberCount += countedMembers[1];
				}
			}
		} else {
			final Map<String, AbstractClassFragment> classSigMap;
			if (!thisClassSigMap.isEmpty()) {
				classSigMap = thisClassSigMap;
			} else if (!otherClassSigMap.isEmpty()) {
				classSigMap = otherClassSigMap;
			} else {
				classSigMap = null;
			}
			if (classSigMap != null) {
				memberCount += classSigMap.size();
				for (AbstractClassFragment classSig : classSigMap.values()) {
					memberCount += classSig.getMemberCount();
				}
			}
		}
		return new int[]{eqMemberCount, memberCount};
	}
	
	public int[] getStatisticsNumbers() {
		int[] counter = new int[2];
		for (AbstractClassFragment curClass : classList.values()) {
			statisticPerClass(curClass, counter);
		}

		int[] counter2 = new int[3];
		counter2[0] = classList.size();
		counter2[1] = counter[0];
		counter2[2] = counter[1];
		return counter2;
	}
	
	public String getStatisticsString() {
		StringBuilder sb = new StringBuilder();
		sb.append("#Classes: ");
		sb.append(classList.size());
		sb.append('\n');

		StringBuilder sb2 = new StringBuilder();
		int[] counter = new int[2];
		for (AbstractClassFragment curClass : classList.values()) {
			sb2.append(statisticPerClass(curClass, counter));
			sb2.append('\n');
		}
		sb.append("#Fields: ");
		sb.append(counter[0]);
		sb.append('\n');
		sb.append("#Methods: ");
		sb.append(counter[1]);
		sb.append('\n');
		sb.append(sb2.toString());
		return sb.toString();
	}
	
	public String getStatisticsStringHeader() {
		StringBuilder sb = new StringBuilder();
		sb.append("#Classes: ");
		sb.append(classList.size());
		sb.append('\n');
		
		int[] counter = new int[2];
		for (AbstractClassFragment curClass : classList.values()) {
			statisticPerClass(curClass, counter);
		}
		sb.append("#Fields: ");
		sb.append(counter[0]);
		sb.append('\n');
		sb.append("#Methods: ");
		sb.append(counter[1]);
		sb.append('\n');
		return sb.toString();
	}
	
	private String statisticPerClass(AbstractClassFragment curClass, int[] counter) {
		StringBuilder sb = new StringBuilder();
		boolean privateSignatures = true;
		
		sb.append(curClass.getSignature().getFullName());
		sb.append('\n');
		
		int numberFields = 0, numberMethods = 0;
		
		for (AbstractSignature memberSig : curClass.getMembers()) {
			if (privateSignatures || !memberSig.isPrivate()) {
				if (memberSig instanceof AbstractFieldSignature) {
					numberFields++;
				} else if (memberSig instanceof AbstractMethodSignature) {
					numberMethods++;
				}
			}
		}

		counter[0] += numberFields;
		counter[1] += numberMethods;
		
		sb.append("\t#Fields: ");
		sb.append(numberFields);
		sb.append('\n');
		
		sb.append("\t#Methods: ");
		sb.append(numberMethods);
		sb.append('\n');
		
		sb.append("\t#Inner Classes: ");
		sb.append(privateSignatures 
				? curClass.getInnerClasses().size() 
				: curClass.getNonPrivateInnerClassCount());
		
		if (!curClass.getInnerClasses().isEmpty()) {
			for (AbstractClassFragment innerClass : curClass.getInnerClasses().values()) {
				sb.append("\n\t");
				sb.append(statisticPerClass(innerClass, counter).replace("\n", "\n\t"));
			}
		}
		
		return sb.toString();
	}
}
