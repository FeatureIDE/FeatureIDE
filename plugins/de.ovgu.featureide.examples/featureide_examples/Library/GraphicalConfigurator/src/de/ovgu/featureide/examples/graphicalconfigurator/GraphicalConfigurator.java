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
package de.ovgu.featureide.examples.graphicalconfigurator;

import java.awt.BorderLayout;
import java.awt.Dimension;
import java.awt.EventQueue;
import java.awt.Toolkit;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.io.IOException;
import java.nio.file.Path;
import java.util.Collections;
import java.util.List;

import javax.swing.DefaultListModel;
import javax.swing.JButton;
import javax.swing.JFileChooser;
import javax.swing.JFrame;
import javax.swing.JLabel;
import javax.swing.JList;
import javax.swing.JMenu;
import javax.swing.JMenuBar;
import javax.swing.JMenuItem;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.JSeparator;
import javax.swing.ListModel;
import javax.swing.ListSelectionModel;
import javax.swing.SwingConstants;
import javax.swing.UIManager;

import de.ovgu.featureide.fm.core.analysis.cnf.formula.FeatureModelFormula;
import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.configuration.ConfigurationAnalyzer;
import de.ovgu.featureide.fm.core.configuration.SelectableFeature;
import de.ovgu.featureide.fm.core.configuration.Selection;
import de.ovgu.featureide.fm.core.configuration.XMLConfFormat;
import de.ovgu.featureide.fm.core.functional.Functional;
import de.ovgu.featureide.fm.core.init.FMCoreLibrary;
import de.ovgu.featureide.fm.core.init.LibraryManager;
import de.ovgu.featureide.fm.core.io.manager.FeatureModelManager;
import de.ovgu.featureide.fm.core.io.manager.FileHandler;
import net.miginfocom.swing.MigLayout;

/**
 * A simple configurator with GUI using the FeatureIDE library.
 *
 * @author Sebastian Krieter
 * @author Thomas Thuem
 */
public class GraphicalConfigurator {

	static {
		LibraryManager.registerLibrary(FMCoreLibrary.getInstance());
	}

	public static void main(String[] args) {
		try {
			UIManager.setLookAndFeel(UIManager.getSystemLookAndFeelClassName());
		} catch (Exception e) {
		}

		EventQueue.invokeLater(new Runnable() {
			public void run() {
				try {
					GraphicalConfigurator.start();
				} catch (Exception e) {
					e.printStackTrace();
				}
			}
		});

	}

	public static void start() {
		final GraphicalConfigurator gui = new GraphicalConfigurator();
		gui.frame.setVisible(true);
	}

	private GraphicalConfigurator() {
		initialize();
	}

	private void initialize() {
		frame = new JFrame();
		frame.setBounds(0, 0, 1280, 720);
		frame.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);

		final Dimension dimension = Toolkit.getDefaultToolkit().getScreenSize();
		int x = (int) ((dimension.getWidth() - frame.getWidth()) / 2);
		int y = (int) ((dimension.getHeight() - frame.getHeight()) / 2);
		frame.setLocation(x, y);

		createMenuBar();
		createHeader();
		createLists();
	}

	private JFrame frame;

	private FeatureModelFormula featureModel;
	private Configuration configuration;
	private ConfigurationAnalyzer configurationAnalyzer;

	private DefaultListModel<Object> undefinedListModel;
	private JList<?> undefinedList;
	private DefaultListModel<Object> selectedListModel;
	private JList<?> selectedList;
	private DefaultListModel<Object> deselectedListModel;
	private JList<?> deselectedList;
	private JLabel featureModelNameLabel;
	private JLabel configurationStatusLabel;

	private void createHeader() {
		featureModelNameLabel = new JLabel("< No Feature Model Specified >");
		configurationStatusLabel = new JLabel("< No Feature Model Specified >");

		JPanel panel = new JPanel();
		panel.setLayout(new MigLayout("", "[left][grow,fill]", "[16px]"));
		panel.add(new JLabel("Feature Model:"), "flowy,cell 0 0,grow");
		panel.add(new JLabel("Configuration Status:"), "cell 0 0");
		panel.add(featureModelNameLabel, "flowy,cell 1 0,grow");
		panel.add(configurationStatusLabel, "cell 1 0");
		panel.add(new JSeparator(), BorderLayout.SOUTH);

		frame.getContentPane().add(panel, BorderLayout.NORTH);
	}

	private void createMenuBar() {
		JMenuItem mntmOpenModelFile = new JMenuItem("Open Model File...");
		mntmOpenModelFile.addActionListener(new ActionListener() {
			@Override
			public void actionPerformed(ActionEvent e) {
				final JFileChooser chooser = new JFileChooser("C:\\skrieter\\workspaces\\local\\runtime-FIDE_001"
				// "C:\\skrieter\\workspaces\\git\\FeatureIDE_develop\\plugins\\de.ovgu.featureide.examples\\featureide_examples"
				);
				if (chooser.showOpenDialog(null) == JFileChooser.APPROVE_OPTION) {
					final Path path = chooser.getSelectedFile().toPath();
					try {
						createEmptyConfiguration(path);
						updateLists();
						updateLabel();
					} catch (IOException e1) {
					}
				}
			}
		});

		JMenuItem mntmSaveConfigFile = new JMenuItem("Save Configuration File...");
		mntmSaveConfigFile.addActionListener(new ActionListener() {
			@Override
			public void actionPerformed(ActionEvent e) {
				JFileChooser chooser = new JFileChooser();
				if (chooser.showSaveDialog(null) == JFileChooser.APPROVE_OPTION) {
					FileHandler.save(chooser.getSelectedFile().toPath(), configuration, new XMLConfFormat());
				}
			}
		});

		JSeparator separator = new JSeparator();
		JMenuItem mntmClose = new JMenuItem("Close");
		mntmClose.addActionListener(new ActionListener() {
			@Override
			public void actionPerformed(ActionEvent e) {
				frame.dispose();
			}
		});

		JMenu mnFile = new JMenu("File");
		mnFile.add(mntmOpenModelFile);
		mnFile.add(mntmSaveConfigFile);
		mnFile.add(separator);
		mnFile.add(mntmClose);

		JMenuBar menuBar = new JMenuBar();
		menuBar.add(mnFile);
		frame.setJMenuBar(menuBar);
	}

	private void createLists() {
		// List 1
		undefinedListModel = new DefaultListModel<>();
		undefinedList = createList(undefinedListModel);
		selectedListModel = new DefaultListModel<>();
		selectedList = createList(selectedListModel);
		deselectedListModel = new DefaultListModel<>();
		deselectedList = createList(deselectedListModel);

		JButton selectButton = new JButton("<-");
		JButton selectRevertButton = new JButton("->");
		JPanel panel_2 = createButtonPanel(selectButton, selectRevertButton);

		JButton deselectButton = new JButton("->");
		JButton deselectRevertButton = new JButton("<-");
		JPanel panel_3 = createButtonPanel(deselectButton, deselectRevertButton);

		selectButton.addActionListener(new ActionListener() {
			public void actionPerformed(ActionEvent event) {
				modifyConfiguration(undefinedList, undefinedListModel, Selection.SELECTED);
			}
		});

		deselectButton.addActionListener(new ActionListener() {
			public void actionPerformed(ActionEvent event) {
				modifyConfiguration(undefinedList, undefinedListModel, Selection.UNSELECTED);
			}
		});

		selectRevertButton.addActionListener(new ActionListener() {
			public void actionPerformed(ActionEvent event) {
				modifyConfiguration(selectedList, selectedListModel, Selection.UNDEFINED);
			}
		});

		deselectRevertButton.addActionListener(new ActionListener() {
			public void actionPerformed(ActionEvent event) {
				modifyConfiguration(deselectedList, deselectedListModel, Selection.UNDEFINED);
			}
		});

		JPanel rootPanel = new JPanel();
		frame.getContentPane().add(rootPanel, BorderLayout.CENTER);
		rootPanel.setLayout(
				new MigLayout("", "[100px:n,grow,fill][60px,center][100px:n,grow,fill][60px,center][100px:n,grow,fill]",
						"[top][grow,fill]"));

		JLabel lblSelected = new JLabel("Selected");
		lblSelected.setHorizontalAlignment(SwingConstants.CENTER);
		rootPanel.add(lblSelected, "cell 0 0");

		JLabel lblNewLabel = new JLabel("Undefined");
		lblNewLabel.setHorizontalAlignment(SwingConstants.CENTER);
		rootPanel.add(lblNewLabel, "cell 2 0");

		JLabel lblDeselected = new JLabel("Deselected");
		lblDeselected.setHorizontalAlignment(SwingConstants.CENTER);
		rootPanel.add(lblDeselected, "cell 4 0");
		rootPanel.add(new JScrollPane(selectedList), "cell 0 1,grow");
		rootPanel.add(panel_2, "cell 1 1,alignx center,growy");
		rootPanel.add(new JScrollPane(undefinedList), "cell 2 1,grow");
		rootPanel.add(panel_3, "cell 3 1,alignx center,growy");
		rootPanel.add(new JScrollPane(deselectedList), "cell 4 1,grow");
	}

	private static JPanel createButtonPanel(JButton selectButton, JButton selectRevertButton) {
		JPanel panel = new JPanel();
		panel.setLayout(new MigLayout("", "[47px,grow]", "[25px][25px][grow]"));
		panel.add(selectButton, "cell 0 0,alignx center,aligny top");
		panel.add(selectRevertButton, "cell 0 1,alignx center,aligny top");
		panel.add(new JPanel(), "cell 0 2,alignx center,growy");
		return panel;
	}

	private static JList<?> createList(ListModel<?> listModel) {
		final JList<?> list = new JList<>(listModel);
		list.setSelectionMode(ListSelectionModel.SINGLE_INTERVAL_SELECTION);
		list.setLayoutOrientation(JList.VERTICAL);
		list.setVisibleRowCount(-1);
		return list;
	}

	private void modifyConfiguration(JList<?> list, DefaultListModel<?> listModel, final Selection selection) {
		final Object selectedValue = list.getSelectedValue();
		if (selectedValue instanceof SelectableFeature) {
			try {
				configuration.setManual((SelectableFeature) selectedValue, selection);
			} catch (Exception e) {
				// ...
				return;
			}
			updateLists();
			if (!listModel.isEmpty()) {
				list.setSelectedIndex(0);
			}
			updateLabel();
		}
	}

	private void updateLabel() {
		configurationStatusLabel.setText(configurationAnalyzer.isValid() ? "Valid" : "Invalid");
	}

	private void updateLists() {
		undefinedListModel.clear();
		selectedListModel.clear();
		deselectedListModel.clear();
		configurationAnalyzer.update(true, null);
		final List<SelectableFeature> features = getSelectableFeatures();
		boolean manualFeatures = true;
		for (SelectableFeature feature : features) {
			if (manualFeatures && feature.getAutomatic() != Selection.UNDEFINED) {
				manualFeatures = false;
				selectedListModel.addElement("-----");
				deselectedListModel.addElement("-----");
			}
			switch (feature.getSelection()) {
			case SELECTED:
				selectedListModel.addElement(feature);
				break;
			case UNDEFINED:
				undefinedListModel.addElement(feature);
				break;
			case UNSELECTED:
				deselectedListModel.addElement(feature);
				break;
			default:
				break;
			}
		}
	}

	private List<SelectableFeature> getSelectableFeatures() {
		final List<SelectableFeature> features = Functional.toList(Functional.filter(configuration.getFeatures(),
				feature -> feature.getFeature().getStructure().isConcrete()
						&& !feature.getFeature().getStructure().hasHiddenParent()));
		Collections.sort(features, (SelectableFeature o1, SelectableFeature o2) -> {
			if (o1.getAutomatic() == Selection.UNDEFINED) {
				if (o2.getAutomatic() == Selection.UNDEFINED) {
					return o1.getName().compareTo(o2.getName());
				} else {
					return -1;
				}
			} else {
				if (o2.getAutomatic() == Selection.UNDEFINED) {
					return 1;
				} else {
					return o1.getName().compareTo(o2.getName());
				}
			}
		});
		return features;
	}

	private void createEmptyConfiguration(final Path path) throws IOException {
		final FileHandler<IFeatureModel> fh = FeatureModelManager.getFileHandler(path);
		if (!fh.getLastProblems().containsError()) {
			featureModel = new FeatureModelFormula(fh.getObject());
			final IFeature root = FeatureUtils.getRoot(featureModel.getFeatureModel());
			if (root != null) {
				featureModelNameLabel.setText(root.getName());
			}

			configuration = new Configuration(featureModel);
			configurationAnalyzer = new ConfigurationAnalyzer(featureModel, configuration);
		} else {
			throw new IOException();
		}
	}

}
