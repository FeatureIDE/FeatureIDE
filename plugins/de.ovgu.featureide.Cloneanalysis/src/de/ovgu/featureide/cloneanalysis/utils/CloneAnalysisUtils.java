package de.ovgu.featureide.cloneanalysis.utils;

import java.io.BufferedReader;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.io.LineNumberReader;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.Path;

import de.ovgu.featureide.cloneanalysis.impl.CloneOccurence;
import de.ovgu.featureide.cloneanalysis.results.CloneAnalysisResults;
import de.ovgu.featureide.cloneanalysis.results.FeatureRootLocation;
import de.ovgu.featureide.cloneanalysis.results.VariantAwareClone;
import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;

public class CloneAnalysisUtils {
	public static IFile getFileFromPath(IPath iPath) {
		return getWorkspaceRoot().getFileForLocation(iPath);
	}

	public static IWorkspaceRoot getWorkspaceRoot() {
		return ResourcesPlugin.getWorkspace().getRoot();
	}

	public static Set<FeatureRootLocation> getRelevantFeatures(CloneAnalysisResults<VariantAwareClone> results) {
		Set<FeatureRootLocation> result = new HashSet<FeatureRootLocation>();
		for (VariantAwareClone clone : results.getClones()) {
			if (clone.getRelevantFeatures() != null && !clone.getRelevantFeatures().isEmpty()) {
				final IProject project = CloneAnalysisUtils.getFileFromPath(clone.getDistinctFiles().get(0))
						.getProject();
				final IFeatureProject featureProject = CorePlugin.getFeatureProject(project);
				if (featureProject != null)
					result.addAll(getIFeaturesFromFeatureFolder(featureProject.getSourceFolder()));
			}

			final Set<IProject> relevantProjects = clone.getRelevantProjects();
			if (relevantProjects != null && !relevantProjects.isEmpty())
				for (final IProject project : relevantProjects)
					result.add(new FeatureRootLocation(project.getLocation()));
		}
		return result;
	}

	public static Collection<? extends FeatureRootLocation> getIFeaturesFromFeatureFolder(IContainer sourceFolder) {
		IResource[] members = null;
		final HashSet<FeatureRootLocation> iFeatures = new HashSet<FeatureRootLocation>();
		try {
			members = sourceFolder.members();
		} catch (CoreException e) {
			e.printStackTrace();
			return iFeatures;
		}
		for (int i = 0; i < members.length; i++) {
			final IResource member = members[i];
			final IPath currentPath = new Path(member.getName());

			if (member instanceof IContainer) {
				final IFolder subFolder = sourceFolder.getFolder(currentPath);
				if (subFolder.exists())
					iFeatures.add(new FeatureRootLocation(subFolder.getLocation()));
			}
			assert false : "Only expected Containers in FeatureProjects source folder";
		}
		return iFeatures;
	}

	public static long countFileLines(IPath path) {
		long lineCount = 0;
		try {
			// LineNumberReader lnr = new LineNumberReader(new
			// FileReader(path.toFile()));
			// lnr.skip(Long.MAX_VALUE);
			// lineCount = lnr.getLineNumber() + 1; //Add 1 because line index
			// starts at 0
			// lnr.close();

			final BufferedReader br = new BufferedReader(new FileReader(path.toFile()));
			String line;
			while ((line = br.readLine()) != null) {
				if (!line.trim().isEmpty()) {
					lineCount++;
				}
			}

		} catch (FileNotFoundException e) {
			e.printStackTrace();
		} catch (IOException e) {
			e.printStackTrace();
		}

		return lineCount;
	}

	public static long getMemberLineSum(IPath path) {
		if (!(getWorkspaceRoot().getContainerForLocation(path) instanceof IContainer))
			assert false : "Path must identify a Container within the current workspace";
		return getMemberLineSum(path, 0);
	}

	private static long getMemberLineSum(IPath path, long c) {
		IContainer countRoot = getWorkspaceRoot().getContainerForLocation(path);
		if (countRoot == null)
			return c;
		IResource[] members = null;
		try {
			members = countRoot.members();
		} catch (CoreException e) {
			e.printStackTrace();
			return c;
		}
		for (int i = 0; i < members.length; i++) {
			final IResource member = members[i];
			final IPath currentPath = new Path(member.getName());

			if (member instanceof IFile) {
				if (member.exists() && member.getName().endsWith(".java"))
					c += countFileLines(member.getLocation());
			} else if (member instanceof IContainer) {
				final IFolder subFolder = countRoot.getFolder(currentPath);
				if (subFolder.exists())
					c += getMemberLineSum(subFolder.getLocation());
			}
		}
		return c;
	}

	public static long getClonedLineCount(FeatureRootLocation feature, Set<VariantAwareClone> clones) {
		long clonedLines = 0;
		for (VariantAwareClone clone : clones) {
			for (CloneOccurence occurence : clone.getOccurences())
				if (feature.getLocation().isPrefixOf(occurence.getFile())) {
					clonedLines += clone.getLineCount();
				}
		}
		return clonedLines;
	}

	public static Map<IFile, short[]> getEmptyMemberLinesMap(FeatureRootLocation feature) {
		return getEmptyMemberLinesMap(new HashMap<IFile, short[]>(), feature.getLocation());
	}

	private static Map<IFile, short[]> getEmptyMemberLinesMap(Map<IFile, short[]> map, IPath path) {
		IContainer countRoot = getWorkspaceRoot().getContainerForLocation(path);
		if (map == null)
			return null;
		IResource[] members = null;
		try {
			members = countRoot.members();
		} catch (CoreException e) {
			e.printStackTrace();
			return map;
		}
		for (int i = 0; i < members.length; i++) {
			final IResource member = members[i];
			final IPath currentPath = new Path(member.getName());

			if (member instanceof IFile) {
				if (member.exists() && member.getName().endsWith(".java"))
					map.put((IFile) member, new short[(int) countFileLines(member.getLocation())]);
			} else if (member instanceof IContainer) {
				final IFolder subFolder = countRoot.getFolder(currentPath);
				if (subFolder.exists())
					map.putAll(getEmptyMemberLinesMap(new HashMap<IFile, short[]>(), member.getLocation()));
			}
		}
		return map;
	}

	public static void calculateClonedLines(Map<FeatureRootLocation, Map<IFile, short[]>> featureClonedLinesPerFile,
			Set<FeatureRootLocation> relevantFeatures, CloneAnalysisResults<VariantAwareClone> results) {
		for (VariantAwareClone clone : results.getClones()) {
			for (CloneOccurence occurence : clone.getOccurences()) {
				final IFile file = getFileFromPath(occurence.getFile());
				for (FeatureRootLocation feature : relevantFeatures) {
					short[] lines = featureClonedLinesPerFile.get(feature).get(file);
					if (lines != null) {
						for (int i = occurence.getStartIndex(); i < (clone.getLineCount() + occurence.getStartIndex())
								&& i < countFileLines(occurence.getFile()); i++) {
							lines[i] = ++(lines[i]);
						}
						featureClonedLinesPerFile.get(feature).remove(file);
						featureClonedLinesPerFile.get(feature).put(file, lines);
					}
				}
			}
		}
	}

	public static String getRelevantFeatureOrProjectName(CloneOccurence occurence) {
		if (occurence.getClone().getRelevantProjects() != null)
			return occurence.getFile().makeRelativeTo(ResourcesPlugin.getWorkspace().getRoot().getLocation())
					.toString();

		// for(IProject project : occurence.getClone().getRelevantProjects())
		// {
		// if(project.getLocation().isPrefixOf(occurence.getFile()))
		// return project.getLocation().lastSegment();
		// }

		// for(FeatureRootLocation featureLocation :
		// ((VariantAwareClone)occurence.getClone()).get)
		// {
		// if(feature.getName()getLocation().isPrefixOf(occurence.getFile()))
		// return project.getLocation().lastSegment();
		// }

		return "unknown";
	}

}
