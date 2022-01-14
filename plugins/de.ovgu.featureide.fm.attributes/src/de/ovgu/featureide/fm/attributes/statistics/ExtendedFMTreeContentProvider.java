package de.ovgu.featureide.fm.attributes.statistics;

import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.jface.viewers.Viewer;

import de.ovgu.featureide.fm.attributes.base.IExtendedFeature;
import de.ovgu.featureide.fm.attributes.base.IExtendedFeatureModel;
import de.ovgu.featureide.fm.attributes.base.IFeatureAttribute;
import de.ovgu.featureide.fm.attributes.computations.IAttributeComputation;
import de.ovgu.featureide.fm.attributes.computations.impl.AttributeComputationBundle;
import de.ovgu.featureide.fm.attributes.computations.impl.ComputationHeader;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.io.manager.ConfigurationManager;
import de.ovgu.featureide.fm.ui.views.outline.custom.OutlineTreeContentProvider;

public class ExtendedFMTreeContentProvider extends OutlineTreeContentProvider {

	private IFeatureModel fModel;
	private Configuration config;

	@Override
	public void inputChanged(Viewer viewer, Object oldInput, Object newInput) {
		if (newInput != null) {
			if (newInput instanceof Configuration) {
				config = ((Configuration) newInput);
				fModel = config.getFeatureModel();
			} else if (newInput instanceof IFile) {
				if (((IFile) newInput).exists()) {
					try {
						ConfigurationManager confManager = ConfigurationManager.getInstance(Paths.get(((IFile) newInput).getLocationURI()));
						config = confManager.getObject();
						fModel = config.getFeatureModel();
					} catch (ClassCastException e) {}
				}
			}
		}
	}

	@Override
	public Object[] getElements(Object inputElement) {
		if (fModel instanceof IExtendedFeatureModel) {
			List<IFeatureAttribute> attributeList = new ArrayList<>();
			for (IFeature feat : fModel.getFeatures()) {
				if (feat instanceof IExtendedFeature) {
					for (IFeatureAttribute att : ((IExtendedFeature) feat).getAttributes()) {
						if (!containsAttribute(attributeList, att.getName())) {
							attributeList.add(att);
						}
					}
				}
			}
			return attributeList.toArray();
		}
		return new String[] { "Please open an extended feature model to use this outline!" };
	}

	@Override
	public Object[] getChildren(Object parentElement) {
		if (parentElement instanceof IFeatureAttribute) {
			AttributeComputationBundle computationBundle = new AttributeComputationBundle();
			// computationBundle.initComputations(config, (IFeatureAttribute) parentElement);
			// return computationBundle.getComputationHeaders().toArray();
		}
		if (parentElement instanceof ComputationHeader) {
			IAttributeComputation[] computations = new IAttributeComputation[1];
			computations[0] = ((ComputationHeader) parentElement).getAttributeComputation();
			return computations;
		}
		return null;
	}

	@Override
	public Object getParent(Object element) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public boolean hasChildren(Object element) {
		if (element instanceof IFeatureAttribute) {
			return true;
		}
		if (element instanceof ComputationHeader) {
			return true;
		}
		return false;
	}

	private boolean containsAttribute(List<IFeatureAttribute> list, String attributeName) {
		for (IFeatureAttribute att : list) {
			if (att.getName().equals(attributeName)) {
				return true;
			}
		}
		return false;
	}

}
