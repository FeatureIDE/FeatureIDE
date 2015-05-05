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
package de.ovgu.featureide.fm.ui.editors.configuration;

import java.util.HashMap;

import org.eclipse.swt.SWT;
import org.eclipse.swt.events.KeyEvent;
import org.eclipse.swt.events.KeyListener;
import org.eclipse.swt.events.MouseEvent;
import org.eclipse.swt.events.MouseListener;
import org.eclipse.swt.events.MouseMoveListener;
import org.eclipse.swt.graphics.GC;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.graphics.ImageData;
import org.eclipse.swt.graphics.Point;
import org.eclipse.swt.layout.FillLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.swt.widgets.Tree;
import org.eclipse.swt.widgets.TreeItem;

import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.configuration.SelectableFeature;
import de.ovgu.featureide.fm.core.configuration.Selection;
import de.ovgu.featureide.fm.ui.FMUIPlugin;
import de.ovgu.featureide.fm.ui.editors.featuremodel.GUIDefaults;

/**
 * Displays the tree for advanced configuration selection at the configuration editor.
 * 
 * @author Jens MeOinicke
 * @author Hannes Smurawsky
 * @author Marcus Pinnecke
 */
public class AdvancedConfigurationPage extends ConfigurationTreeEditorPage implements GUIDefaults {
	private static final String PAGE_TEXT = "Advanced Configuration";
	private static final String ID = FMUIPlugin.PLUGIN_ID + "AdvancedConfigurationPage";

	private static HashMap<String, Image> combinedImages = new HashMap<String, Image>();

	private static Image getImage(SelectableFeature selFeature, Selection selection) {
		final Feature feature = selFeature.getFeature();

		final Image image1 = getConnectionImage(feature);
		final Image image2 = getSelectionImage(selFeature, selection);

		final ImageData imageData1 = image1.getImageData();
		final ImageData imageData2 = image2.getImageData();

		final String imageString = image1.toString() + image2.toString();

		final Image combinedImage = combinedImages.get(imageString);
		if (combinedImage == null) {
			final int distance = 5;
			final Image mergeImage = new Image(image1.getDevice(), imageData2.width * 2 + distance, imageData1.height);

			final GC gc = new GC(mergeImage);

			if (image1.equals(IMG_MANDATORY) || image1.equals(IMG_OPTIONAL)) {
				gc.drawImage(image1, 0, 0, imageData1.width, imageData1.height, 3, 3, imageData1.width, imageData1.height);
			} else {
				gc.drawImage(image1, 0, 0, imageData1.width, imageData1.height, 0, 0, imageData1.width, imageData1.height);
			}
			gc.drawImage(image2, 0, 0, imageData2.width, imageData2.height, imageData1.width + distance, 0, imageData2.width, imageData2.height);

			gc.dispose();

			if (feature.isRoot()) {
				image1.dispose();
			}

			combinedImages.put(imageString, mergeImage);
			return mergeImage;
		}
		return combinedImage;
	}

	private static Image getConnectionImage(Feature feature) {
		if (!feature.isRoot()) {
			if (feature.getParent() != null) {
				if (feature.getParent().isOr()) {
					return IMG_OR;
				}
				if (feature.getParent().isAlternative()) {
					return IMG_XOR;
				}
			}
			if (feature.isMandatory()) {
				return IMG_MANDATORY;
			}
			return IMG_OPTIONAL;
		}
		return new Image(null, IMG_MANDATORY.getImageData().width, IMG_MANDATORY.getImageData().height);
	}

	private static Image getSelectionImage(SelectableFeature feat, Selection selection) {
		if (selection != null) {
			switch (selection) {
			case SELECTED:
				return IMAGE_ASELECTED;
			case UNSELECTED:
				return IMAGE_ADESELECTED;
			case UNDEFINED:
				return IMAGE_UNDEFINED;
			}
		}
		if (feat.getAutomatic() != Selection.UNDEFINED) {
			return feat.getAutomatic() == Selection.SELECTED ? IMAGE_ASELECTED : IMAGE_ADESELECTED;
		}
		switch (feat.getManual()) {
		case SELECTED:
			return IMAGE_SELECTED;
		case UNSELECTED:
			return IMAGE_DESELECTED;
		case UNDEFINED:
		default:
			return IMAGE_UNDEFINED;
		}
	}

	protected void createUITree(Composite parent) {
		tree = new Tree(parent, SWT.NONE);
		tree.addMouseListener(new MouseListener() {
			@Override
			public void mouseUp(MouseEvent e) {
				if (e.button == 1 || e.button == 3) {
					TreeItem item = tree.getItem(new Point(e.x, e.y));
					if (item != null) {
						final Object data = item.getData();
						if (data instanceof SelectableFeature) {
							final SelectableFeature feature = (SelectableFeature) item.getData();
							item.setImage(getImage(feature, null));
							if (updateFeatures.contains(feature)) {
								item.setImage(getImage(feature, Selection.SELECTED));
							} else if (feature.getAutomatic() == Selection.UNDEFINED) {
								changeSelection(item, e.button == 1);
							}
						}
					}
				}
			}

			@Override
			public void mouseDown(MouseEvent e) {
			}

			@Override
			public void mouseDoubleClick(MouseEvent e) {
			}
		});
		tree.addKeyListener(new KeyListener() {
			public void keyPressed(KeyEvent e) {
				if (e.character == ' ') {
					final TreeItem[] selection = tree.getSelection();
					if (selection.length > 0) {
						final TreeItem item = selection[0];
						final Object data = item.getData();
						if (data instanceof SelectableFeature) {
							final SelectableFeature feature = (SelectableFeature) item.getData();
							item.setImage(getImage(feature, null));
							if (updateFeatures.contains(feature)) {
								item.setImage(getImage(feature, Selection.SELECTED));
							} else if (feature.getAutomatic() == Selection.UNDEFINED) {
								cycleSelection(feature, true);
							}
						}
					}
				}
			}

			public void keyReleased(KeyEvent e) {
			}
		});
		tree.addMouseMoveListener(new MouseMoveListener() {
			@Override
			public void mouseMove(MouseEvent e) {
				final TreeItem item = tree.getItem(new Point(e.x, e.y));
				long currentTime = System.currentTimeMillis();
				boolean changed = false;
				if (item == null || item != tipItem) {
					//					time = currentTime;
					tipItem = item;
					changed = true;
				}

				if (tip == null) {
					if (item != null) {
						createTooltip(item, e, currentTime);
					}
				} else {
					if (item == null) {
						disposeTooltip();
					} else if (changed) {
						disposeTooltip();
						createTooltip(item, e, currentTime);
					}
				}
			}
		});
	}

	private TreeItem tipItem = null;
	private Shell tip = null;

	//	private long time = 0;

	private void disposeTooltip() {
		if (tip != null) {
			tip.dispose();
			tip = null;
		}
	}

	private void createTooltip(TreeItem item, MouseEvent e, long currentTime) {
		//		if (time + 500 > currentTime) {
		//			return;
		//		}
		final Object data = item.getData();
		if (data instanceof SelectableFeature) {
			final SelectableFeature feature = (SelectableFeature) item.getData();
			final String relConst = feature.getFeature().getRelevantConstraintsString();
			final String describ = feature.getFeature().getDescription();
			final StringBuilder sb = new StringBuilder();

			if (describ != null) {
				sb.append("Description:\n");
				sb.append(describ);
			}
			if (!relConst.isEmpty()) {
				if (sb.length() > 0) {
					sb.append("\n\n");
				}
				sb.append("Constraints:\n");
				sb.append(relConst);
			}
			if (sb.length() > 0) {
				tipItem = item;
				tip = new Shell(tree.getShell(), SWT.ON_TOP | SWT.TOOL);
				FillLayout fillLayout = new FillLayout();
				fillLayout.marginHeight = 1;
				fillLayout.marginWidth = 1;
				tip.setLayout(fillLayout);
				Label label = new Label(tip, SWT.NONE);
				label.setForeground(tip.getDisplay().getSystemColor(SWT.COLOR_INFO_FOREGROUND));
				label.setBackground(tip.getDisplay().getSystemColor(SWT.COLOR_INFO_BACKGROUND));
				label.setText(sb.toString());
				Point size = tip.computeSize(SWT.DEFAULT, SWT.DEFAULT);
				Point pt = tree.toDisplay(e.x, e.y);
				tip.setBounds(pt.x, pt.y + 26, size.x, size.y);
				tip.setVisible(true);
			}
		}
	}

	protected void refreshItem(TreeItem item, SelectableFeature feature) {
		item.setBackground(null);
		item.setForeground(null);
		item.setFont(treeItemStandardFont);
		item.setImage(getImage(feature, null));
		if (feature.getAutomatic() == Selection.UNSELECTED) {
			item.setForeground(gray);
		}
	}

	@Override
	protected void lockItem(TreeItem item) {
		item.setImage(getImage((SelectableFeature) item.getData(), Selection.SELECTED));
		item.setFont(treeItemStandardFont);
		item.setForeground(gray);
	}

	@Override
	public String getID() {
		return ID;
	}

	@Override
	public String getPageText() {
		return PAGE_TEXT;
	}

	@Override
	protected boolean canDeselectFeatures() {
		return true;
	}

	private void cycleSelection(SelectableFeature feature, boolean up) {
		if (feature.getAutomatic() == Selection.UNDEFINED) {
			switch (feature.getManual()) {
			case SELECTED:
				set(feature, (up) ? Selection.UNSELECTED : Selection.UNDEFINED);
				break;
			case UNSELECTED:
				set(feature, (up) ? Selection.UNDEFINED : Selection.SELECTED);
				break;
			case UNDEFINED:
				set(feature, (up) ? Selection.SELECTED : Selection.UNSELECTED);
				break;
			default:
				set(feature, Selection.UNDEFINED);
			}
			if (!dirty) {
				setDirty();
			}
		}
	}
}
