import java.util.LinkedList;
import java.util.List;

import org.prop4j.Node;

import de.ovgu.featureide.fm.core.Constraint;
import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;


//public class FeatureModelCounter extends FeatureModel {
//	int count = 1;
//	
//	@Override
//	public FeatureModelCounter clone() {
//		FeatureModelCounter fm = new FeatureModelCounter();
//		fm.root = root != null ? root.clone() : new Feature(fm, "Root");
//		List<Feature> list = new LinkedList<Feature>();
//		list.add(fm.root);
//		while (!list.isEmpty()) {
//			Feature feature = list.remove(0);
//			fm.featureTable.put(feature.getName(), feature);
//			for (Feature child : feature.getChildren())
//				list.add(child);
//		}
//		fm.propNodes = new LinkedList<Node>();
//		for (Node node : propNodes) {
//			fm.propNodes.add(node);
//
//			fm.constraints.add(new Constraint(fm, node));
//		}
//		for (int i = 0; i < annotations.size(); i++)
//			fm.annotations.add(annotations.get(i));
//		for (int i = 0; i < comments.size(); i++)
//			fm.comments.add(comments.get(i));
//		fm.colorschemeTable = colorschemeTable.clone(fm);
//		return fm;
//	}

public class FeatureModelCounter {
	
	Double hashCode;
	int count;
	String model;
	public FeatureModelCounter(Double hashCode, String model) {
		this.hashCode = hashCode;
		this.model = model;
		count = 1;
	}
	public FeatureModelCounter(Double hashCode) {
		this.hashCode = hashCode;
	}
	@Override
	public boolean equals(Object obj) {
		return hashCode.equals(obj);
	}

}
