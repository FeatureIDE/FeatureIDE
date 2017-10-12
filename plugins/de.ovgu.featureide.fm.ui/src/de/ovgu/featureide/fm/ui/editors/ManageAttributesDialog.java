/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2017  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.fm.ui.editors;

import static de.ovgu.featureide.fm.core.localization.StringTable.MANAGE_ATTRIBUTES;

import java.awt.GridBagConstraints;
import java.awt.GridBagLayout;
import java.awt.Insets;
import java.awt.Toolkit;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;

import javax.swing.JButton;
import javax.swing.JComboBox;
import javax.swing.JDialog;
import javax.swing.JLabel;
import javax.swing.JPanel;
import javax.swing.JTextField;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.jface.dialogs.Dialog;
import org.eclipse.jface.viewers.CellEditor;
import org.eclipse.jface.viewers.ColumnViewerEditor;
import org.eclipse.jface.viewers.ColumnViewerEditorActivationEvent;
import org.eclipse.jface.viewers.ColumnViewerEditorActivationStrategy;
import org.eclipse.jface.viewers.EditingSupport;
import org.eclipse.jface.viewers.FocusCellOwnerDrawHighlighter;
import org.eclipse.jface.viewers.ILabelProviderListener;
import org.eclipse.jface.viewers.ITableLabelProvider;
import org.eclipse.jface.viewers.ITreeContentProvider;
import org.eclipse.jface.viewers.ITreeSelection;
import org.eclipse.jface.viewers.TextCellEditor;
import org.eclipse.jface.viewers.TreePath;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.jface.viewers.TreeViewerColumn;
import org.eclipse.jface.viewers.TreeViewerEditor;
import org.eclipse.jface.viewers.TreeViewerFocusCellManager;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.graphics.Point;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Event;
import org.eclipse.swt.widgets.Listener;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.swt.widgets.TreeColumn;
import org.eclipse.swt.widgets.TreeItem;
import org.eclipse.ui.progress.UIJob;

import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureStructure;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent.EventType;
import de.ovgu.featureide.fm.core.base.impl.FeatureAttribute;
import de.ovgu.featureide.fm.core.base.impl.FeatureAttributeInherited;

/**
 * Dialog to show FeatureModel in TreeViewer and add, delete and edit FeatureAttributes
 *
 * @author "Werner Jan"
 */
public class ManageAttributesDialog extends Dialog {

	private final IFeatureModel featureModel;
	private final String[] columLabels = { "Feature", "Attributename", "Value", "Type", "Unit", "Configurable", "Recursive" };

	public ManageAttributesDialog(final Shell parentShell, IFeatureModel featureModel) {
		super(parentShell);
		this.featureModel = featureModel;
	}

	/**
	 * Sets the minimal size and the text in the title of the dialog.
	 *
	 * @param newshell
	 */
	@Override
	protected void configureShell(Shell newShell) {
		super.configureShell(newShell);
		newShell.setText(MANAGE_ATTRIBUTES);
	}

	@Override
	protected Point getInitialSize() {
		return new Point(1300, 1000);
	}

	/**
	 * Creates the general layout of the dialog.
	 *
	 * @param parent
	 */
	@Override
	protected Control createDialogArea(Composite parent) {
		final Composite container = (Composite) super.createDialogArea(parent);
		container.setBackground(new Color(parent.getDisplay(), 255, 255, 255));
		final GridLayout gridLayout = new GridLayout();
		gridLayout.numColumns = 2;
		container.setLayout(gridLayout);

		final TreeViewer viewer = new TreeViewer(container, SWT.BORDER | SWT.MULTI);
		GridData gridData = new GridData();
		gridData.horizontalSpan = 2;
		gridData.horizontalAlignment = GridData.FILL;
		gridData.grabExcessHorizontalSpace = true;
		gridData.verticalAlignment = SWT.FILL;
		gridData.grabExcessVerticalSpace = true;
		viewer.getTree().setLayoutData(gridData);
		viewer.getTree().setHeaderVisible(true);
		viewer.getTree().setLinesVisible(true);

		final TreeViewerFocusCellManager focusCellManager = new TreeViewerFocusCellManager(viewer, new FocusCellOwnerDrawHighlighter(viewer));
		final ColumnViewerEditorActivationStrategy actSupport = new ColumnViewerEditorActivationStrategy(viewer) {

			@Override
			protected boolean isEditorActivationEvent(ColumnViewerEditorActivationEvent event) {
				return (event.eventType == ColumnViewerEditorActivationEvent.TRAVERSAL)
					|| (event.eventType == ColumnViewerEditorActivationEvent.MOUSE_DOUBLE_CLICK_SELECTION)
					|| ((event.eventType == ColumnViewerEditorActivationEvent.KEY_PRESSED) && (event.keyCode == SWT.CR))
					|| (event.eventType == ColumnViewerEditorActivationEvent.PROGRAMMATIC);
			}
		};

		final int feature = ColumnViewerEditor.TABBING_HORIZONTAL | ColumnViewerEditor.TABBING_MOVE_TO_ROW_NEIGHBOR | ColumnViewerEditor.TABBING_VERTICAL
			| ColumnViewerEditor.KEYBOARD_ACTIVATION;

		// Create the columns for the TreeViewer

		TreeViewerEditor.create(viewer, focusCellManager, actSupport, feature);
		final CellEditor textCellEditor = new TextCellEditor(viewer.getTree());

		final TreeViewerColumn column0 = new TreeViewerColumn(viewer, SWT.NONE);
		column0.getColumn().setWidth(120);
		column0.getColumn().setMoveable(true);
		column0.getColumn().setText(columLabels[0]);
		column0.setEditingSupport(createEditingSupportFor(viewer, textCellEditor));

		final TreeViewerColumn column1 = new TreeViewerColumn(viewer, SWT.NONE);
		column1.getColumn().setWidth(150);
		column1.getColumn().setMoveable(true);
		column1.getColumn().setText(columLabels[1]);
		column1.setEditingSupport(new GivenNameEditing(viewer));

		final TreeViewerColumn column2 = new TreeViewerColumn(viewer, SWT.NONE);
		column2.getColumn().setWidth(150);
		column2.getColumn().setMoveable(true);
		column2.getColumn().setText(columLabels[2]);
		column2.setEditingSupport(new GivenValueEditing(viewer));

		final TreeViewerColumn column3 = new TreeViewerColumn(viewer, SWT.NONE);
		column3.getColumn().setWidth(150);
		column3.getColumn().setMoveable(true);
		column3.getColumn().setText(columLabels[3]);
		column3.setEditingSupport(new GivenTypeEditing(viewer));

		final TreeViewerColumn column4 = new TreeViewerColumn(viewer, SWT.NONE);
		column4.getColumn().setWidth(150);
		column4.getColumn().setMoveable(true);
		column4.getColumn().setText(columLabels[4]);
		column4.setEditingSupport(new GivenUnitEditing(viewer));

		final TreeViewerColumn column5 = new TreeViewerColumn(viewer, SWT.NONE);
		column5.getColumn().setWidth(150);
		column5.getColumn().setMoveable(true);
		column5.getColumn().setText(columLabels[5]);
		column5.setEditingSupport(new GivenConfigurableEditing(viewer));

		final TreeViewerColumn column6 = new TreeViewerColumn(viewer, SWT.NONE);
		column6.getColumn().setWidth(150);
		column6.getColumn().setMoveable(true);
		column6.getColumn().setText(columLabels[6]);
		column6.setEditingSupport(new GivenRecursiveEditing(viewer));

		viewer.setContentProvider(new MyContentProvider());
		viewer.setLabelProvider(new TableLabelProvider());

		/**
		 * Create "Add"-Button to add attributes, get the selected Feature and create Dialog
		 */

		final Button bAdd = new Button(container, SWT.NONE);
		bAdd.setText("Add Attribute");
		bAdd.addSelectionListener(new SelectionListener() {

			@Override
			public void widgetDefaultSelected(SelectionEvent e) {

			}

			@Override
			public void widgetSelected(SelectionEvent e) {
				final ITreeSelection selection = viewer.getStructuredSelection();
				final TreePath[] selected = selection.getPaths();

				Object f;

				if ((selected[0].getLastSegment() instanceof FeatureAttribute) || (selected[0].getLastSegment() instanceof FeatureAttributeInherited)) {
					f = selected[0].getSegment(selected[0].getSegmentCount() - 2);
				} else {
					f = selected[0].getLastSegment();
				}

				if (f instanceof IFeature) {
					final JDialog dialog = new JDialog();
					dialog.setTitle("Add new Attribute");
					createDialog(dialog, ((IFeature) f), featureModel);
				}

			}

			/**
			 *
			 * Creates a new Dialog to add FeatureAttributes to a selected IFeature.
			 *
			 * ActionListener checks the input and marks TextFields if input incorrect and shows a tooltip.
			 *
			 * @param dialog Add Attributes Dialog
			 * @param feature selected IFeature
			 * @param featureModel
			 */
			private void createDialog(final JDialog dialog, final IFeature feature, final IFeatureModel featureModel) {

				dialog.setLayout(new GridBagLayout());
				dialog.setResizable(false);
				final JLabel jLabel = new JLabel("Selected Feature: " + feature.getName());

				final GridBagConstraints gridBagConstraints = new GridBagConstraints();

				gridBagConstraints.insets = new Insets(5, 0, 5, 0);

				gridBagConstraints.gridx = 0;
				gridBagConstraints.gridy = 0;

				dialog.add(jLabel, gridBagConstraints);

				gridBagConstraints.gridy++;

				final JPanel jPanel = new JPanel();
				final JLabel jName = new JLabel("Name: ");
				jPanel.add(jName);
				final JTextField textFieldName = new JTextField(20);
				jPanel.add(textFieldName, gridBagConstraints);
				dialog.add(jPanel, gridBagConstraints);
				gridBagConstraints.gridy++;

				final JPanel jPanelValue = new JPanel();
				final JLabel jLabelValue = new JLabel("Value: ");
				final JTextField textFieldValue = new JTextField(20);
				jPanelValue.add(jLabelValue);
				jPanelValue.add(textFieldValue);
				dialog.add(jPanelValue, gridBagConstraints);

				gridBagConstraints.gridy++;

				final JPanel jPanelUnit = new JPanel();
				final JLabel jLabelUnit = new JLabel("Unit: ");
				final JTextField textFieldUnit = new JTextField(20);
				jPanelUnit.add(jLabelUnit);
				jPanelUnit.add(textFieldUnit);
				dialog.add(jPanelUnit, gridBagConstraints);
				gridBagConstraints.gridy++;

				final String[] Types = { "String", "Long", "Double", "Boolean" };
				final JPanel jPanelType = new JPanel();
				final JLabel jLabelType = new JLabel("Type: ");
				final JComboBox<String> typeBox = new JComboBox<String>(Types);

				jPanelType.add(jLabelType);
				jPanelType.add(typeBox);
				dialog.add(jPanelType, gridBagConstraints);

				gridBagConstraints.gridy++;

				final String[] bools = { "false", "true" };
				final JPanel jPanelRecursive = new JPanel();
				final JLabel jLabelRecursive = new JLabel("Recursive: ");
				final JComboBox<String> recursiveBox = new JComboBox<String>(bools);
				typeBox.setSelectedIndex(1);

				jPanelRecursive.add(jLabelRecursive);
				jPanelRecursive.add(recursiveBox);
				dialog.add(jPanelRecursive, gridBagConstraints);

				gridBagConstraints.gridy++;

				final JPanel jPanelConfigurable = new JPanel();
				final JLabel jLabelConfigurable = new JLabel("Configurable: ");
				final JComboBox<String> configurableBox = new JComboBox<String>(bools);

				jPanelConfigurable.add(jLabelConfigurable);
				jPanelConfigurable.add(configurableBox);
				dialog.add(jPanelConfigurable, gridBagConstraints);

				gridBagConstraints.gridy++;

				final JButton bCancel = new JButton("Cancel");
				bCancel.addActionListener(new ActionListener() {

					@Override
					public void actionPerformed(ActionEvent e) {
						dialog.dispose();
					}
				});
				final JButton bAdd = new JButton("Add");
				bAdd.addActionListener(new ActionListener() {

					@Override
					public void actionPerformed(ActionEvent e) {

						textFieldName.setBackground(java.awt.Color.white);
						textFieldValue.setBackground(java.awt.Color.white);
						textFieldUnit.setBackground(java.awt.Color.white);
						
						textFieldName.setToolTipText(null);
						textFieldValue.setToolTipText(null);
						textFieldUnit.setToolTipText(null);

						final String name = textFieldName.getText().trim();
						String value = textFieldValue.getText().trim();
						if (value == null) {
							value = "";
						}
						final String type = typeBox.getSelectedItem().toString().trim();
						final String unit = textFieldUnit.getText().trim();
						final String recursive = recursiveBox.getSelectedItem().toString().trim();
						final String configurable = configurableBox.getSelectedItem().toString().trim();

						final boolean rec = recursive.equals("true");
						final boolean conf = configurable.equals("true");

						boolean allGood = true;

						if (name.isEmpty()) {
							textFieldName.setBackground(java.awt.Color.red);
							textFieldName.setToolTipText("Every attribute needs a name.");
							allGood = false;
						} else {
							final String nameLowerCase = name.toLowerCase();
							for (final FeatureAttribute fa : feature.getStructure().getAttributeList()) {
								if (fa.getName().toLowerCase().equals(nameLowerCase)) {
									textFieldName.setBackground(java.awt.Color.red);
									textFieldName.setToolTipText("There already is an attribute with that name.");
									allGood = false;
								}
							}
							for (final FeatureAttributeInherited fai : feature.getStructure().getAttributeListInherited()) {
								if (fai.getName().toLowerCase().equals(nameLowerCase)) {
									textFieldName.setBackground(java.awt.Color.red);
									allGood = false;
									textFieldName.setToolTipText("There already is an attribute with that name.");
								}
							}
							if (rec) {
								for (final IFeatureStructure iFeature : feature.getStructure().getChildren()) {
									for (final FeatureAttribute fa : iFeature.getAttributeList()) {
										if (fa.getName().toLowerCase().equals(nameLowerCase)) {
											allGood = false;
											textFieldName.setToolTipText("There is an attribute in a child with that name, can't create recursive attribute.");
										}
									}
								}
							}
						}

						final FeatureAttribute attribute = new FeatureAttribute(name, value, type, unit, rec, conf);

						if (!attribute.checkValue()) {
							textFieldValue.setBackground(java.awt.Color.red);
							textFieldValue.setToolTipText("The value doesn't match the type.");
							allGood = false;
						}
						if (allGood) {
							featureModel.getFeature(feature.getName()).getStructure().getAttributeList().add(attribute);
							if (rec) {
								feature.getStructure().updateFeatureAttributeInherited(attribute);
							}
							featureModel.fireEvent(new FeatureIDEEvent(featureModel, EventType.FEATURE_ATTRIBUTE_ADDED));

							final UIJob job = new UIJob("New Attribute Added") {

								@Override
								public IStatus runInUIThread(IProgressMonitor monitor) {
									viewer.setInput(featureModel);
									return Status.OK_STATUS;
								}
							};
							job.schedule();
							dialog.dispose();
						}
					}
				});

				final JPanel jpButton = new JPanel();
				jpButton.add(bCancel);
				jpButton.add(bAdd);
				dialog.add(jpButton, gridBagConstraints);

				dialog.pack();
				dialog.setSize(350, 400);
				dialog.setLocation((Toolkit.getDefaultToolkit().getScreenSize().width - dialog.getWidth()) / 2,
						(Toolkit.getDefaultToolkit().getScreenSize().height - dialog.getHeight()) / 2);
				dialog.setVisible(true);
			}

		});

		final Button bRemove = new Button(container, SWT.NONE);
		gridData = new GridData();
		bRemove.setLayoutData(gridData);
		bRemove.setText("Remove Attribute");
		bRemove.addSelectionListener(new SelectionListener() {

			@Override
			public void widgetDefaultSelected(SelectionEvent e) {

			}

			@Override
			public void widgetSelected(SelectionEvent e) {
				final ITreeSelection selection = viewer.getStructuredSelection();
				final Object selectedFeatureAttribute = selection.getFirstElement();
				if (selectedFeatureAttribute instanceof FeatureAttribute) {

					final List<String> featureNameList = featureModel.getFeatureOrderList();
					for (int i = 0; i < featureNameList.size(); i++) {
						final IFeature feature = featureModel.getFeature(featureNameList.get(i));
						final LinkedList<FeatureAttribute> featureAttributeList = feature.getStructure().getAttributeList();
						final LinkedList<FeatureAttributeInherited> featureAttributeInheritedList = feature.getStructure().getAttributeListInherited();
						for (final FeatureAttributeInherited featureAttributeInherited : featureAttributeInheritedList) {
							if (featureAttributeInherited.getParent().equals(selectedFeatureAttribute)) {
								featureAttributeInheritedList.remove(featureAttributeInherited);
							}
						}
						for (final FeatureAttribute featureAttribute : featureAttributeList) {
							if (featureAttribute.equals(selectedFeatureAttribute)) {
								featureAttributeList.remove(selectedFeatureAttribute);
							}
						}
					}
					viewer.refresh();
				}
			}

		});

		/**
		 * Dynamically growing columns
		 */
		viewer.getControl();
		final Listener listener = new Listener() {

			@Override
			public void handleEvent(Event event) {
				final TreeItem treeItem = (TreeItem) event.item;
				final TreeColumn[] treeColumns = treeItem.getParent().getColumns();
				Display.getCurrent().asyncExec(new Runnable() {

					@Override
					public void run() {
						treeColumns[0].pack();
					}
				});
			}
		};
		viewer.getTree().addListener(SWT.Expand, listener);
		viewer.setInput(featureModel);
		viewer.expandToLevel(3);
		return parent;

	}

	private class MyContentProvider implements ITreeContentProvider {

		@Override
		public Object[] getElements(Object inputElement) {
			final IFeatureModel fm = (IFeatureModel) inputElement;
			final ArrayList<IFeature> feature = new ArrayList<IFeature>();
			final IFeature name = fm.getStructure().getRoot().getFeature();
			feature.add(name);
			if (fm.getNumberOfFeatures() == 0) {
				return new Object[0];
			}
			return feature.toArray();
		}

		@Override
		public void dispose() {}

		@Override
		public void inputChanged(Viewer viewer, Object oldInput, Object newInput) {}

		@Override
		public Object[] getChildren(Object parentElement) {
			final ArrayList<Object> feature = new ArrayList<Object>();
			LinkedList<FeatureAttribute> attList = new LinkedList<>();
			LinkedList<FeatureAttributeInherited> attListInh = new LinkedList<>();
			if (parentElement instanceof IFeature) {
				final IFeature f = (IFeature) parentElement;
				attList = f.getStructure().getAttributeList();
				attListInh = f.getStructure().getAttributeListInherited();
				for (final FeatureAttribute attribute : attList) {
					feature.add(attribute);

				}
				for (final FeatureAttributeInherited attributeInh : attListInh) {
					if (!isInList(attList, attributeInh.getParent())) {
						feature.add(attributeInh);
					}
				}
				for (int i = 0; i < f.getStructure().getChildrenCount(); i++) {
					final IFeature cf = f.getStructure().getChildren().get(i).getFeature();
					feature.add(cf);
				}
			}
			return feature.toArray();
		}

		@Override
		public Object getParent(Object element) {
			if (element instanceof IFeature) {
				return ((IFeature) element).getStructure().getParent().getFeature();
			}
			return null;
		}

		@Override
		public boolean hasChildren(Object element) {
			if (element instanceof IFeature) {
				final IFeature f = (IFeature) element;
				if (f.getStructure().hasChildren()) {
					return true;
				} else if ((f.getStructure().getAttributeList() != null) || (f.getStructure().getAttributeListInherited() != null)) {
					return true;
				}
			}
			return false;
		}

		private boolean isInList(LinkedList<FeatureAttribute> attList, FeatureAttribute inhAtt) {
			for (final FeatureAttribute attribute : attList) {
				if (attribute.equals(inhAtt)) {
					return true;
				}
			}
			return false;
		}
	}

	class TableLabelProvider implements ITableLabelProvider {

		/**
		 * Dynamically growing columns
		 */

		@Override
		public Image getColumnImage(Object element, int columnIndex) {
			return null;
		}

		@Override
		public String getColumnText(Object element, int columnIndex) {
			switch (columnIndex) {
			case 0:
				if (element instanceof IFeature) {
					return ((IFeature) element).getName();
				}
				if (element instanceof FeatureAttribute) {
					return "Attribute";
				}
				if (element instanceof FeatureAttributeInherited) {
					return "Inherited attribute";
				}
			case 1:
				if (element instanceof FeatureAttribute) {
					return ((FeatureAttribute) element).getName();
				}
				if (element instanceof FeatureAttributeInherited) {
					return ((FeatureAttributeInherited) element).getName();
				}
			case 2:
				if (element instanceof FeatureAttribute) {
					return ((FeatureAttribute) element).getValue();
				}
				if (element instanceof FeatureAttributeInherited) {
					return ((FeatureAttributeInherited) element).getValue();
				}

			case 3:
				if (element instanceof FeatureAttribute) {
					return ((FeatureAttribute) element).getTypeString();
				}
				if (element instanceof FeatureAttributeInherited) {
					return ((FeatureAttributeInherited) element).getParent().getTypeString();
				}

			case 4:
				if (element instanceof FeatureAttribute) {
					return ((FeatureAttribute) element).getUnit();
				}
				if (element instanceof FeatureAttributeInherited) {
					return ((FeatureAttributeInherited) element).getParent().getUnit();
				}

			case 5:
				if (element instanceof FeatureAttribute) {
					return String.valueOf(((FeatureAttribute) element).getConfigurable());
				}
				if (element instanceof FeatureAttributeInherited) {
					return String.valueOf(((FeatureAttributeInherited) element).getParent().getConfigurable());
				}

			case 6:
				if (element instanceof FeatureAttribute) {
					return String.valueOf(((FeatureAttribute) element).getRecursive());
				}
				if (element instanceof FeatureAttributeInherited) {
					return String.valueOf(((FeatureAttributeInherited) element).getParent().getRecursive());
				}
			}
			return null;
		}

		@Override
		public void addListener(ILabelProviderListener listener) {

		}

		@Override
		public void dispose() {

		}

		@Override
		public boolean isLabelProperty(Object element, String property) {
			return false;
		}

		@Override
		public void removeListener(ILabelProviderListener listener) {

		}
	}

	private EditingSupport createEditingSupportFor(final TreeViewer viewer, final CellEditor textCellEditor) {
		return new EditingSupport(viewer) {

			@Override
			protected boolean canEdit(Object element) {
				return true;
			}

			@Override
			protected CellEditor getCellEditor(Object element) {
				return textCellEditor;
			}

			@Override
			protected Object getValue(Object element) {
				return null;
			}

			@Override
			protected void setValue(Object element, Object value) {
				viewer.update(element, null);
			}
		};
	}

	private class GivenNameEditing extends EditingSupport {

		private final TextCellEditor cellEditor;

		public GivenNameEditing(TreeViewer viewer) {
			super(viewer);
			cellEditor = new TextCellEditor(viewer.getTree());
		}

		@Override
		protected boolean canEdit(Object element) {
			return true;
		}

		@Override
		protected CellEditor getCellEditor(Object element) {
			return cellEditor;
		}

		@Override
		protected Object getValue(Object element) {
			return ((FeatureAttribute) element).getName();
		}

		@Override
		protected void setValue(Object element, Object value) {
			((FeatureAttribute) element).setName(value.toString());
			getViewer().update(element, null);
			getViewer().refresh();
		}
	}

	private class GivenValueEditing extends EditingSupport {

		private final TextCellEditor cellEditor;

		public GivenValueEditing(TreeViewer viewer) {
			super(viewer);
			cellEditor = new TextCellEditor(viewer.getTree());
		}

		@Override
		protected boolean canEdit(Object element) {
			return true;
		}

		@Override
		protected CellEditor getCellEditor(Object element) {
			return cellEditor;
		}

		@Override
		protected Object getValue(Object element) {
			if (element instanceof FeatureAttribute) {
				return ((FeatureAttribute) element).getValue();
			}
			if (element instanceof FeatureAttributeInherited) {
				return ((FeatureAttributeInherited) element).getValue();
			}
			return null;
		}

		@Override
		protected void setValue(Object element, Object value) {
			if (element instanceof FeatureAttribute) {
				((FeatureAttribute) element).setValue(value.toString());
				getViewer().update(element, null);
			}
			if (element instanceof FeatureAttributeInherited) {
				((FeatureAttributeInherited) element).setValue(value.toString());
				getViewer().update(element, null);
			}
		}
	}

	private class GivenTypeEditing extends EditingSupport {

		private final TextCellEditor cellEditor;

		public GivenTypeEditing(TreeViewer viewer) {
			super(viewer);
			cellEditor = new TextCellEditor(viewer.getTree());
		}

		@Override
		protected boolean canEdit(Object element) {
			return true;
		}

		@Override
		protected CellEditor getCellEditor(Object element) {
			return cellEditor;
		}

		@Override
		protected Object getValue(Object element) {
			return ((FeatureAttribute) element).getTypeNames();
		}

		@Override
		protected void setValue(Object element, Object value) {
			((FeatureAttribute) element).setTypeFromString(value.toString());
			getViewer().update(element, null);
		}
	}

	private class GivenUnitEditing extends EditingSupport {

		private final TextCellEditor cellEditor;

		public GivenUnitEditing(TreeViewer viewer) {
			super(viewer);
			cellEditor = new TextCellEditor(viewer.getTree());
		}

		@Override
		protected boolean canEdit(Object element) {
			return true;
		}

		@Override
		protected CellEditor getCellEditor(Object element) {
			return cellEditor;
		}

		@Override
		protected Object getValue(Object element) {
			return ((FeatureAttribute) element).getUnit();
		}

		@Override
		protected void setValue(Object element, Object value) {
			((FeatureAttribute) element).setUnit(value.toString());
			getViewer().update(element, null);
			getViewer().refresh();
		}
	}

	private class GivenConfigurableEditing extends EditingSupport {

		private final TextCellEditor cellEditor;

		public GivenConfigurableEditing(TreeViewer viewer) {
			super(viewer);
			cellEditor = new TextCellEditor(viewer.getTree());
		}

		@Override
		protected boolean canEdit(Object element) {
			return true;
		}

		@Override
		protected CellEditor getCellEditor(Object element) {
			return cellEditor;
		}

		@Override
		protected Object getValue(Object element) {
			return String.valueOf(((FeatureAttribute) element).getConfigurable());
		}

		@Override
		protected void setValue(Object element, Object value) {
			((FeatureAttribute) element).setConfigurable((value.toString()));
			getViewer().update(element, null);
			getViewer().refresh();
		}
	}

	private class GivenRecursiveEditing extends EditingSupport {

		private final TextCellEditor cellEditor;

		public GivenRecursiveEditing(TreeViewer viewer) {
			super(viewer);
			cellEditor = new TextCellEditor(viewer.getTree());
		}

		@Override
		protected boolean canEdit(Object element) {
			return true;
		}

		@Override
		protected CellEditor getCellEditor(Object element) {
			return cellEditor;
		}

		@Override
		protected Object getValue(Object element) {
			return String.valueOf(((FeatureAttribute) element).getRecursive());
		}

		@Override
		protected void setValue(Object element, Object value) {
			if (value.toString().toLowerCase().equals("true")) {
				((FeatureAttribute) element).setRecursive(true);
			} else if (value.toString().toLowerCase().equals("false")) {
				((FeatureAttribute) element).setRecursive(false);
			} else {
				try {
					Boolean.parseBoolean((String) value);
				} catch (final Exception e) {

				}
			}

			getViewer().update(element, null);
			getViewer().refresh();
		}
	}
}
