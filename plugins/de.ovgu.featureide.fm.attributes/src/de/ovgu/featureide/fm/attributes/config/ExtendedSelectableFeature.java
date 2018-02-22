package de.ovgu.featureide.fm.attributes.config;

import java.util.HashMap;
import java.util.Map;

import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.configuration.SelectableFeature;

/**
 * 
 * Extension of a selectable feature (Features in the context of a configuiration) Attaches map with attribute values which were changed in the configuration
 * 
 * @author Chico Sundermann
 */

public class ExtendedSelectableFeature extends SelectableFeature {

	// Store name and value as string
	private Map<String, String> configurableAttributes = new HashMap<String, String>();

	public ExtendedSelectableFeature(IFeature feature) {
		super(feature);
	}

	public ExtendedSelectableFeature(IFeature feature, Map<String, String> confAtt) {
		super(feature);
		this.configurableAttributes = confAtt;
	}

	/**
	 *
	 * @return Map<Name of the attribute, value of the attribute>
	 */
	public Map<String, String> getConfigurableAttributes() {
		return configurableAttributes;
	}

	/**
	 * Adds a name/ value pair to the configured attributes map
	 * 
	 * @param name
	 * @param value
	 */
	public void addConfigurableAttribute(String name, String value) {
		configurableAttributes.put(name, value);
	}

	@Override
	public void cloneProperties(SelectableFeature feat) {
		if (feat instanceof ExtendedSelectableFeature) {
			configurableAttributes = ((ExtendedSelectableFeature) feat).getConfigurableAttributes();
		}
	}

}
