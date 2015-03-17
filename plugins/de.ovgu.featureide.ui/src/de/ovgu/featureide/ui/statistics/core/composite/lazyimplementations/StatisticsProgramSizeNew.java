package de.ovgu.featureide.ui.statistics.core.composite.lazyimplementations;

import java.io.BufferedReader;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.HashSet;
import java.util.LinkedList;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IResourceVisitor;
import org.eclipse.core.runtime.CoreException;
import de.ovgu.featureide.core.fstmodel.FSTClass;
import de.ovgu.featureide.core.fstmodel.FSTClassFragment;
import de.ovgu.featureide.core.fstmodel.FSTField;
import de.ovgu.featureide.core.fstmodel.FSTMethod;
import de.ovgu.featureide.core.fstmodel.FSTModel;
import de.ovgu.featureide.core.fstmodel.FSTRole;
import de.ovgu.featureide.ui.UIPlugin;
import de.ovgu.featureide.ui.statistics.core.composite.LazyParent;

/**
 * TreeNode who stores the number of classes, roles, fields and methods of a
 * given {@link FSTModel}.<br>
 * This node should only be used for a feature oriented project.
 * 
 * @author Schleicher Miro
 */
public class StatisticsProgramSizeNew extends LazyParent {

	private final FSTModel fstModel;
	int numberOfLines = 0;

	public StatisticsProgramSizeNew(String description, FSTModel fstModel) {
		super(description);
		this.fstModel = fstModel;
	}

	@Override
	protected void initChildren() {

		int numberOfClasses = 0;
		int numberOfRoles = 0;
		int numberOfFields = 0;
		int numberOfUniFields = 0;
		int numberOfMethods = 0;
		int numberOfUniMethods = 0;

		for (FSTClass fstClass : fstModel.getClasses()) {
			final LinkedList<LinkedList<FSTClassFragment>> allFrag = fstClass.getAllFSTFragments();
			final HashSet<FSTMethod> methHelper = new HashSet<FSTMethod>();
			final HashSet<FSTField> fieldHelper = new HashSet<FSTField>();

			for (LinkedList<FSTClassFragment> linkedList : allFrag) {
				numberOfRoles += linkedList.size();

				for (FSTClassFragment fstClassFragment : linkedList) {
					methHelper.addAll(fstClassFragment.getMethods());
					fieldHelper.addAll(fstClassFragment.getFields());

					numberOfMethods += fstClassFragment.getMethods().size();
					numberOfFields += fstClassFragment.getFields().size();
				}
			}

			numberOfUniFields += fieldHelper.size();
			numberOfUniMethods += methHelper.size();
			numberOfClasses += allFrag.size();
		}

		if (fstModel.getFeatureProject().getComposer().hasFeatureFolder()) {
			final LinkedHashSet<String> extList = fstModel.getFeatureProject().getComposer().extensions();
			try {
				fstModel.getFeatureProject().getSourceFolder().accept(new IResourceVisitor() {

					@Override
					public boolean visit(IResource resource) throws CoreException {
						if (resource instanceof IFolder) {
							return true;
						} else if (resource instanceof IFile) {
							final IFile file = (IFile) resource;
							String oneLineComment = "", moreLineStart = "", moreLineEnd = "";
							boolean nested = false;
							int nestedCounter = 0;
							switch (file.getFileExtension()) {
							case "java" :
							case "c" :	
							case "h" :	
									oneLineComment = "//";
									moreLineStart = "/*";
									moreLineEnd = "*/";
									nested = false;
									nestedCounter = 0;
								break;
							case "cs" : 
									oneLineComment = "///";
									moreLineStart = "/*";
									moreLineEnd = "*/";
									nested = false;
									nestedCounter = 0;
								break;
							case "hs" :
									oneLineComment = "--";
									moreLineStart = "{-";
									moreLineEnd = "-}";
									nested = true;
									nestedCounter = 0;
								break;	
							default:
								oneLineComment ="#|#|#";
								moreLineStart = "#|#|#";
								moreLineEnd = "#|#|#";
								nested = false;
								nestedCounter = 0;
								break;
							}
							
							try {
								FileReader fr = new FileReader(file.getLocation().toString());
								BufferedReader br = new BufferedReader(fr);
								String s;
								boolean isInComment = false;
								while ((s = br.readLine()) != null) {
									if (s.trim().contains(moreLineEnd)) {
										if(nested) {
											nestedCounter--;
											if(nestedCounter == 0)
												isInComment = false;
										} else {
											isInComment = false;
										}
									}
										

									if (!s.trim().equals("") && !s.trim().startsWith(oneLineComment) && !isInComment) {
										if (s.trim().startsWith(moreLineStart))//TODO Kommentare sind auf java bezogen noch sprachunabhängig implementieren
											isInComment = true;
										else
											numberOfLines++;
									}

									if (s.trim().contains(moreLineStart))
										isInComment = true;
								}
								br.close();

							} catch (FileNotFoundException e) {
								e.printStackTrace();
							} catch (IOException e) {
								e.printStackTrace();
							}
						}

						return false;
					}
				});
			} catch (CoreException e) {
				UIPlugin.getDefault().logError(e);
			}
		}

		
//		extensions.add("hs");
//		extensions.add("jj");
//		extensions.add("als");
//		extensions.add("xmi");
		
		addChild(new SumImplementationArtifactsParent(NUMBER_CLASS + SEPARATOR + numberOfClasses + " | " + NUMBER_ROLE + SEPARATOR + numberOfRoles, fstModel,
				SumImplementationArtifactsParent.NUMBER_OF_CLASSES));
		addChild(new SumImplementationArtifactsParent(NUMBER_FIELD_U + SEPARATOR + numberOfUniFields + " | " + NUMBER_FIELD + SEPARATOR + numberOfFields,
				fstModel, SumImplementationArtifactsParent.NUMBER_OF_FIELDS));
		addChild(new SumImplementationArtifactsParent(NUMBER_METHOD_U + SEPARATOR + numberOfUniMethods + " | " + NUMBER_METHOD + SEPARATOR + numberOfMethods,
				fstModel, SumImplementationArtifactsParent.NUMBER_OF_METHODS));
		addChild(new SumImplementationArtifactsParent(NUMBER_OF_CODELINES + SEPARATOR + numberOfLines, fstModel,
				SumImplementationArtifactsParent.NUMBER_OF_LINES));
	}
}
