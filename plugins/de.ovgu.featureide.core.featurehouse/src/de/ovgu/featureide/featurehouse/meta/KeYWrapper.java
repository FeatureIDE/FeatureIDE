/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2015  FeatureIDE team, University of Magdeburg, Germany
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
 * See http://featureide.cs.ovgu.de/ for further information.
 */
package de.ovgu.featureide.featurehouse.meta;

import java.io.File;
import java.io.IOException;
import java.lang.reflect.Constructor;
import java.lang.reflect.InvocationHandler;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.lang.reflect.Proxy;
import java.util.LinkedList;

import org.eclipse.core.internal.runtime.InternalPlatform;
import org.osgi.framework.Bundle;

import de.ovgu.featureide.core.fstmodel.FSTFeature;
import de.ovgu.featureide.core.signature.ProjectSignatures;
import de.ovgu.featureide.featurehouse.FeatureHouseCorePlugin;

/**
 * Wrapper for KeY
 * 
 * @author Stefan Krueger
 * @author Sebastian Krieter
 */
@SuppressWarnings("restriction")
public class KeYWrapper {

	private static final boolean isKeYLoaded;
	private static Class<?> mainClass, keYMediatorClass, guilClass, uiClass;
	static {
		Bundle bundleKeYStarter = null;
		for (Bundle b : InternalPlatform.getDefault().getBundleContext().getBundles()) {
			if (b.getSymbolicName().equals("org.key_project.key4eclipse")) {
				bundleKeYStarter = b;
				break;
			}
		}
		boolean isKeYLoadedtmp = false;

		try {
			if (bundleKeYStarter != null) {
				org.osgi.framework.BundleActivator act = ((org.osgi.framework.BundleActivator) bundleKeYStarter.loadClass(
						"org.key_project.key4eclipse.Activator").newInstance());
				act.start(InternalPlatform.getDefault().getBundleContext());

				mainClass = bundleKeYStarter.loadClass("de.uka.ilkd.key.gui.Main");
				keYMediatorClass = bundleKeYStarter.loadClass("de.uka.ilkd.key.gui.KeYMediator");
				guilClass = bundleKeYStarter.loadClass("de.uka.ilkd.key.gui.GUIListener");
				uiClass = bundleKeYStarter.loadClass("de.uka.ilkd.key.ui.UserInterface");

				isKeYLoadedtmp = mainClass != null && keYMediatorClass != null && guilClass != null && uiClass != null;
			}
		} catch (RuntimeException e) {
			throw e;
		} catch (Exception e) {
			FeatureHouseCorePlugin.getDefault().logError(e);
		} finally {
			isKeYLoaded = isKeYLoadedtmp;
		}

	}

	private Object guiL;

	public static KeYWrapper createGUIListener(final FeatureStubsGenerator featureStubsGenerator, final ProjectSignatures signatures,
			final LinkedList<FSTFeature> features) {
		return (isKeYLoaded) ? new KeYWrapper(featureStubsGenerator, signatures, features) : null;
	}

	private KeYWrapper(final FeatureStubsGenerator featureStubsGenerator, final ProjectSignatures signatures,
			final LinkedList<FSTFeature> features) {
		final InvocationHandler h = new InvocationHandler() {
			@Override
			public Object invoke(Object proxy, Method method, Object[] args) throws Throwable {
				if (method.getName().equals("shutDown")) {
					featureStubsGenerator.nextElement(signatures, features);
				}
				return null;
			}
		};
		final Class<?> proxyguiL = Proxy.getProxyClass(guilClass.getClassLoader(), guilClass);
		try {
			guiL = proxyguiL.getConstructor(InvocationHandler.class).newInstance((Object) h);
		} catch (InstantiationException | IllegalAccessException | IllegalArgumentException | InvocationTargetException
				| NoSuchMethodException | SecurityException e) {
			e.printStackTrace();
		}

	}

	public void runKeY(File file) throws IOException {
		try {
			Constructor<?> mainC = mainClass.getConstructor(String[].class);
			Object key = mainC.newInstance((Object) (new String[] { file.getCanonicalPath() }));
			Method getGui = mainClass.getMethod("getUi");
			Object ui = getGui.invoke(key);
			if (ui != null) {
				Method getMediator = uiClass.getMethod("getMediator");
				Method addGuiListener = keYMediatorClass.getMethod("addGUIListener", guilClass);
				addGuiListener.invoke(getMediator.invoke(ui), guiL);
			} else {
				FeatureHouseCorePlugin.getDefault().logError("KeY could not be started.", null);
			}
		} catch (IllegalAccessException | IllegalArgumentException | InvocationTargetException | NoSuchMethodException | SecurityException
				| InstantiationException e) {
			FeatureHouseCorePlugin.getDefault().logError("KeY could not be started.", e);
		}
	}

}
