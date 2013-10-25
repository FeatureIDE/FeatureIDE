package de.ovgu.featureide.core.mpl.io;

import org.eclipse.core.resources.IProject;

import de.ovgu.featureide.core.mpl.InterfaceProject;
import de.ovgu.featureide.core.mpl.MPLPlugin;
import de.ovgu.featureide.core.mpl.io.reader.ExtendedConfigurationReader;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.io.xml.XmlFeatureModelReader;

public final class FileLoader {

	public static Configuration loadConfiguration(
			InterfaceProject interfaceProject) {
		try {
			ExtendedConfigurationReader exConfReader = new ExtendedConfigurationReader(interfaceProject);
			return exConfReader.read();
		} catch (Exception e) {
			MPLPlugin.getDefault().logError(e);
			return null;
		}
	}

	public static FeatureModel loadFeatureModel(IProject project) {
		try {
			FeatureModel featureModel = new FeatureModel();
			XmlFeatureModelReader reader = new XmlFeatureModelReader(featureModel);
			reader.readFromFile(project.getFile(IOConstants.FILENAME_MODEL).getLocation().toFile());
			return featureModel;
		} catch (Exception e) {
			MPLPlugin.getDefault().logError(e);
			return null;
		}
	}

//	public static RoleMap loadRoleMap(InterfaceProject interfaceProject) {
//		RoleMap roleMap = new RoleMap(interfaceProject);
//		try {
//			IFolder mainFolder = interfaceProject.getProjectReference()
//					.getFolder(IOConstants.FOLDERNAME_FEATURE_ROLES);
//			if (mainFolder.isAccessible()) {
//				InterfaceParser parser = new InterfaceParser(
//						interfaceProject.getViewTagPool(), roleMap);
//
//				for (IResource featureFolder : mainFolder.members()) {
//					if (featureFolder instanceof IFolder) {
//						parser.setFeatureName(featureFolder.getName());
//						for (IResource featureFolderMember : ((IFolder) featureFolder)
//								.members()) {
//							if (featureFolderMember instanceof IFolder) {
//								IFolder packageFolder = (IFolder) featureFolderMember;
//								for (IResource file : packageFolder.members()) {
//									parser.setFile((IFile) file);
//									roleMap.addRole(parser.read());
//								}
//							} else if (featureFolderMember instanceof IFile) {
//								parser.setFile((IFile) featureFolderMember);
//								roleMap.addRole(parser.read());
//							}
//						}
//					}
//				}
//			}
//			MPLPlugin.getDefault().logInfo("Local RoleMap loaded.");
//			return roleMap;
//		} catch (CoreException e) {
//			MPLPlugin.getDefault().logError(e);
//			return null;
//		}
//	}
}
