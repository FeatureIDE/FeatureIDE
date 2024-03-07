/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2019  FeatureIDE team, University of Magdeburg, Germany
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

import static de.ovgu.featureide.fm.core.localization.StringTable.ADVANCED_CONFIGURATION;

import java.util.Collection;

import org.eclipse.jface.action.Action;
import org.eclipse.jface.action.IMenuListener;
import org.eclipse.jface.action.IMenuManager;
import org.eclipse.jface.action.MenuManager;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.KeyEvent;
import org.eclipse.swt.events.KeyListener;
import org.eclipse.swt.events.MouseEvent;
import org.eclipse.swt.events.MouseListener;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.graphics.GC;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.graphics.ImageData;
import org.eclipse.swt.graphics.Point;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Menu;
import org.eclipse.swt.widgets.Tree;
import org.eclipse.swt.widgets.TreeItem;

import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.color.ColorPalette;
import de.ovgu.featureide.fm.core.color.FeatureColor;
import de.ovgu.featureide.fm.core.color.FeatureColorManager;
import de.ovgu.featureide.fm.core.configuration.SelectableFeature;
import de.ovgu.featureide.fm.core.configuration.Selection;
import de.ovgu.featureide.fm.ui.FMUIPlugin;
import de.ovgu.featureide.fm.ui.GraphicsExporter;
import de.ovgu.featureide.fm.ui.editors.featuremodel.GUIDefaults;

/**
 * Displays the tree for advanced configuration selection at the configuration editor.
 *
 * @author Jens Meinicke
 * @author Hannes Smurawsky
 * @author Marcus Pinnecke
 */
public class AdvancedConfigurationPage extends ConfigurationTreeEditorPage implements GUIDefaults {

	private static final String PAGE_TEXT = ADVANCED_CONFIGURATION;
	private static final String ID = FMUIPlugin.PLUGIN_ID + "AdvancedConfigurationPage";

	private static Image getImage(SelectableFeature selFeature, Selection selection) {
		final IFeature feature = selFeature.getFeature();

		final Image image1 = getConnectionImage(feature);
		final Image image2 = getSelectionImage(selFeature, selection);

		final ImageData imageData1 = image1.getImageData();
		final ImageData imageData2 = image2.getImageData();

		final int distance = 4;
		final int colorWidth = 24;
		final int colorHeight = 12;

		final ImageData id =
			new Image(Display.getCurrent(), imageData2.width + distance + imageData1.width + distance + colorWidth + distance, imageData1.height)
					.getImageData();
		id.alpha = 0;
		final Image mergeImage = new Image(Display.getCurrent(), id);

		final GC gc = new GC(mergeImage);

		final FeatureColor color = FeatureColorManager.getColor(feature);

		gc.drawImage(image2, 0, 0, imageData2.width, imageData2.height, 0, 0, imageData2.width, imageData2.height);
		gc.drawImage(image1, 0, 0, imageData1.width, imageData1.height, imageData2.width + distance, 0, imageData1.width, imageData1.height);
		if (color != FeatureColor.NO_COLOR) {
			gc.setBackground(new Color(null, ColorPalette.getRGB(color.getValue(), 0.5f)));
			gc.fillRoundRectangle(imageData2.width + distance + imageData1.width + distance, (imageData1.height - colorHeight) / 2, colorWidth, colorHeight,
					colorHeight, colorHeight);
		} else {
			gc.setForeground(new Color(191, 191, 191));
			gc.drawRoundRectangle(imageData2.width + distance + imageData1.width + distance, (imageData1.height - colorHeight) / 2, colorWidth, colorHeight,
					colorHeight, colorHeight);
		}

		return mergeImage;
	}

	private static Image getConnectionImage(IFeature feature) {
		if (!feature.getStructure().isRoot()) {
			if (feature.getStructure().getParent() != null) {
				if (feature.getStructure().getParent().isOr()) {
					return IMG_OR;
				}
				if (feature.getStructure().getParent().isAlternative()) {
					return IMG_XOR;
				}
			}
			if (feature.getStructure().isMandatory()) {
				return IMG_MANDATORY;
			}
			return IMG_OPTIONAL;
		}
		final ImageData id = new Image(Display.getCurrent(), IMG_MANDATORY.getImageData().width, IMG_MANDATORY.getImageData().height).getImageData();
		id.alpha = 0;
		return new Image(Display.getCurrent(), id);
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

	@Override
	protected void createUITree(Composite parent) {
		tree = new Tree(parent, SWT.NONE);
		final MenuManager contextMenu = new MenuManager(null);
		contextMenu.setRemoveAllWhenShown(true);
		contextMenu.addMenuListener(new IMenuListener() {

			@Override
			public void menuAboutToShow(IMenuManager mgr) {
				contextMenu.add(new Action("Export As...", IMAGE_EXPORT_AS) {

					@Override
					public void run() {
						GraphicsExporter.exportAs(configurationEditor.getConfigurationManager().getSnapshot());
					}
				});
			}
		});
		final Menu createContextMenu = contextMenu.createContextMenu(tree);

		tree.addMouseListener(new MouseListener() {

			@Override
			public void mouseUp(MouseEvent e) {
				if ((e.button == 1) || (e.button == 3)) {
					final TreeItem item = tree.getItem(new Point(e.x, e.y));
					if (item != null) {
						final Object data = item.getData();
						if (data instanceof SelectableFeature) {
							final SelectableFeature feature = (SelectableFeature) item.getData();
							item.setImage(getImage(feature, null));
							if (updateFeatures.contains(feature)) {
								item.setImage(getImage(feature, Selection.SELECTED));
							} else {
								changeSelection(item, e.button == 1);
							}
						}
					}
				}
			}

			@Override
			public void mouseDown(MouseEvent e) {
				if (tree.getItem(new Point(e.x, e.y)) != null) {
					tree.setMenu(null);
				} else {
					tree.setMenu(createContextMenu);
				}
			}

			@Override
			public void mouseDoubleClick(MouseEvent e) {}
		});
		tree.addKeyListener(new KeyListener() {

			@Override
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
							} else {
								cycleSelection(item, true);
							}
						}
					}
				}
			}

			@Override
			public void keyReleased(KeyEvent e) {}
		});
	}

	@Override
	protected void refreshItem(Collection<TreeItem> items) {
		super.refreshItem(items);
		for (final TreeItem item : items) {
			final Object data = item.getData();
			if (data instanceof SelectableFeature) {
				final SelectableFeature feature = (SelectableFeature) data;
				item.setImage(getImage(feature, null));
			}
		}
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

	protected void cycleSelection(TreeItem item, boolean up) {
		final Selection manualSelection = ((SelectableFeature) item.getData()).getManual();
		switch (manualSelection) {
		case SELECTED:
			setManual(item, (up) ? Selection.UNSELECTED : Selection.UNDEFINED);
			break;
		case UNSELECTED:
			setManual(item, (up) ? Selection.UNDEFINED : Selection.SELECTED);
			break;
		case UNDEFINED:
			setManual(item, (up) ? Selection.SELECTED : Selection.UNSELECTED);
			break;
		default:
			throw new AssertionError(manualSelection);
		}
	}

}
