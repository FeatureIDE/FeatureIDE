package de.ovgu.featureide.ui.views.collaboration.outline;

import org.eclipse.jface.action.Action;
import org.eclipse.jface.viewers.ITreeContentProvider;

public class ProviderAction extends Action {
	
	private ITreeContentProvider treeProv = null;
	private OutlineLabelProvider lableProv = null;
	
	public ProviderAction(String name, int type, ITreeContentProvider treeProv, OutlineLabelProvider prov){
		super("", AS_RADIO_BUTTON);

		this.setText(name);
		this.treeProv = treeProv;
		this.lableProv = prov;
		
	}
	
	public ITreeContentProvider getTreeContentProvider(){
		return treeProv;
	}
	
	public OutlineLabelProvider getLabelProvider() {
		return lableProv;
	}
}
