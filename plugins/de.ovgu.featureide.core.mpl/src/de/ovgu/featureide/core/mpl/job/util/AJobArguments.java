package de.ovgu.featureide.core.mpl.job.util;

import java.lang.reflect.Constructor;

import de.ovgu.featureide.core.mpl.MPLPlugin;

public abstract class AJobArguments {
	
	private final Constructor<? extends IChainJob> constructor;
	
	@SuppressWarnings("unchecked")
	protected AJobArguments(Class<? extends AJobArguments> cl) {
		Constructor<? extends IChainJob> temp;
		try {
			temp = (Constructor<? extends IChainJob>) cl.getEnclosingClass().getDeclaredConstructor(cl);
			temp.setAccessible(true);
		} catch (Exception e) {
			MPLPlugin.getDefault().logError(e);
			temp = null;
		}
		constructor = temp;
	}
	
	public IChainJob createJob() {
		if (constructor == null) {
			return null;
		}
		try {
			return constructor.newInstance(this);
		} catch (Exception e) {
			MPLPlugin.getDefault().logError(e);
			return null;
		}
	}
}
