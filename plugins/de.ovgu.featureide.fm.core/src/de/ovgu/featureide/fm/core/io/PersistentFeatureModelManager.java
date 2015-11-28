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
package de.ovgu.featureide.fm.core.io;

import java.io.File;
import java.nio.charset.Charset;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.nio.file.StandardOpenOption;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import de.ovgu.featureide.fm.core.FMCorePlugin;
import de.ovgu.featureide.fm.core.base.FactoryMananger;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.io.xml.XmlFeatureModelHandler;

/**
 * TODO description
 * 
 * @author Sebastian Krieter
 */
public class PersistentFeatureModelManager {

	private static Map<String, PersistentFeatureModelManager> map = new HashMap<>();

	private final IFeatureModel featureModel;

	private final List<Exception> lastExceptions = new LinkedList<>();

	private final List<IPersistentHandler> extraHandlers = new ArrayList<>();
	private final IPersistentHandler modelHandler;

	private final Path modelPath;
	private final Path extraFolder;

	private final String fileName;

	public static PersistentFeatureModelManager getInstance(String path) {
		return getInstance(path, null);
	}

	public static PersistentFeatureModelManager getInstance(String path, IFeatureModel model) {
		final Path p = Paths.get(path).toAbsolutePath();
		final String absolutePath = p.toString();
		PersistentFeatureModelManager persistentFeatureModelManager = map.get(absolutePath);
		if (persistentFeatureModelManager == null) {
			if (model == null) {
				model = FactoryMananger.getFactory().createFeatureModel();
			}
			model.setSourceFile(new File(absolutePath));
			persistentFeatureModelManager = new PersistentFeatureModelManager(model, absolutePath);
		}
		return persistentFeatureModelManager;
	}

	private PersistentFeatureModelManager(IFeatureModel featureModel, String absolutePath) {
		this.featureModel = featureModel;
		this.modelHandler = new XmlFeatureModelHandler(featureModel);

		final File modelFile = featureModel.getSourceFile();
		if (modelFile == null) {
			throw new NullPointerException("No source file specified");
		}

		map.put(absolutePath, this);

		modelPath = Paths.get(absolutePath);
		fileName = modelPath.getFileName().toString();
		final Path root = modelPath.getRoot();
		extraFolder = root.resolve(modelPath.subpath(0, modelPath.getNameCount() - 1).resolve("." + fileName));
	}

	public void addHandler(IPersistentHandler handler) {
		extraHandlers.add(handler);
	}

	private Path getExtraPath(IPersistentHandler iPersistentFormat) {
		return extraFolder.resolve(fileName + "." + iPersistentFormat.getSuffix());
	}

	public IFeatureModel getFeatureModel() {
		return featureModel;
	}

	public List<Exception> getLastExceptions() {
		return lastExceptions;
	}

	private void internalRead() throws Exception {
		try {
			read(modelHandler, modelPath);
		} catch (Exception e) {
			lastExceptions.add(e);
			FMCorePlugin.getDefault().logError(e);
			return;
		}

		if (Files.exists(extraFolder)) {
			for (final IPersistentHandler iPersistentFormat : extraHandlers) {
				try {
					read(iPersistentFormat);
				} catch (final Exception e) {
					lastExceptions.add(e);
					FMCorePlugin.getDefault().logError(e);
				}
			}
		}
	}

	private void internalSave() throws Exception {
		if (!Files.exists(extraFolder)) {
			Files.createDirectory(extraFolder);
		}

		try {
			save(modelHandler, modelPath);
		} catch (Exception e) {
			lastExceptions.add(e);
			FMCorePlugin.getDefault().logError(e);
			return;
		}

		for (IPersistentHandler iPersistentFormat : extraHandlers) {
			try {
				save(iPersistentFormat);
			} catch (Exception e) {
				lastExceptions.add(e);
				FMCorePlugin.getDefault().logError(e);
			}
		}
	}

	public boolean read() {
		lastExceptions.clear();
		try {
			internalRead();
		} catch (Exception e) {
			lastExceptions.add(e);
			FMCorePlugin.getDefault().logError(e);
		}
		return lastExceptions.isEmpty();
	}

	public void read(IPersistentHandler iPersistentFormat) throws Exception {
		final String content = new String(Files.readAllBytes(getExtraPath(iPersistentFormat)), Charset.availableCharsets().get("UTF-8"));
		iPersistentFormat.read(content);
	}

	private void read(IPersistentHandler iPersistentFormat, Path file) throws Exception {
		final String content = new String(Files.readAllBytes(file), Charset.availableCharsets().get("UTF-8"));
		iPersistentFormat.read(content);
	}

	public void removeHandler(IPersistentHandler handler) {
		extraHandlers.remove(handler);
	}

	public boolean save() {
		lastExceptions.clear();
		try {
			internalSave();
		} catch (Exception e) {
			lastExceptions.add(e);
			FMCorePlugin.getDefault().logError(e);
		}
		return lastExceptions.isEmpty();
	}

	public void save(IPersistentHandler iPersistentFormat) throws Exception {
		final byte[] content = iPersistentFormat.write().getBytes(Charset.availableCharsets().get("UTF-8"));
		Files.write(getExtraPath(iPersistentFormat), content, StandardOpenOption.CREATE, StandardOpenOption.WRITE);
	}

	private void save(IPersistentHandler iPersistentFormat, Path file) throws Exception {
		final byte[] content = iPersistentFormat.write().getBytes(Charset.availableCharsets().get("UTF-8"));
		Files.write(file, content, StandardOpenOption.CREATE, StandardOpenOption.WRITE);
	}

}
