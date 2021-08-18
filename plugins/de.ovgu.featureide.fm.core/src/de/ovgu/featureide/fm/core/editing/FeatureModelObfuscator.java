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
package de.ovgu.featureide.fm.core.editing;

import java.nio.charset.StandardCharsets;
import java.security.MessageDigest;
import java.security.SecureRandom;

import org.prop4j.Literal;
import org.prop4j.Node;

import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureModelFactory;
import de.ovgu.featureide.fm.core.base.IFeatureStructure;
import de.ovgu.featureide.fm.core.base.impl.FMFactoryManager;
import de.ovgu.featureide.fm.core.functional.Base32Encoder;
import de.ovgu.featureide.fm.core.job.LongRunningMethod;
import de.ovgu.featureide.fm.core.job.monitor.IMonitor;
import de.ovgu.featureide.fm.core.localization.StringTable;

/**
 * Returns a copy of the given model with obfuscated feature names and descriptions.
 *
 * @author Sebastian Krieter
 * @author Rahel Arens
 * @author Benedikt Jutz
 */
public class FeatureModelObfuscator implements LongRunningMethod<IFeatureModel> {

	private final static SecureRandom secureRandom = new SecureRandom();

	private final static int LENGTH_FACTOR = 8;
	protected static final int RESULT_LENGTH = (4 * LENGTH_FACTOR);

	protected final IFeatureModel orgFeatureModel;
	protected final IFeatureModelFactory factory;
	private final byte[] salt;

	protected MessageDigest digest;
	protected IFeatureModel obfuscatedFeatureModel;

	/**
	 * Instantiates the obfuscater with a default salt value (Not recommended!). Alternatively, {@link #FeatureModelObfuscator(IFeatureModel, String)} can be
	 * used to set a salt value.
	 *
	 * @param featureModel the feature model to be obfuscated
	 */
	public FeatureModelObfuscator(IFeatureModel featureModel) {
		this(featureModel, "");
	}

	/**
	 * Instantiates the obfuscater using the given feature model and salt value.
	 *
	 * @param featureModel the feature model to be obfuscated
	 * @param salt a fix salt value
	 */
	public FeatureModelObfuscator(IFeatureModel featureModel, String salt) {
		this.salt = salt.getBytes(StandardCharsets.UTF_8);
		orgFeatureModel = featureModel;
		factory = FMFactoryManager.getInstance().getFactory(orgFeatureModel);
	}

	@Override
	public IFeatureModel execute(IMonitor<IFeatureModel> monitor) throws Exception {
		digest = MessageDigest.getInstance(StringTable.SHA_256_DIGEST_ALGORITHM);
		obfuscatedFeatureModel = factory.create();
		obfuscateStructure(orgFeatureModel.getStructure().getRoot(), null);
		obfuscateConstraints();
		return obfuscatedFeatureModel;
	}

	private void obfuscateStructure(IFeatureStructure orgFeatureStructure, IFeature parentFeature) {
		final IFeature orgFeature = orgFeatureStructure.getFeature();

		final IFeature obfuscatedFeature = factory.createFeature(obfuscatedFeatureModel, getObfuscatedFeatureName(orgFeature.getName()));
		final String description = orgFeatureStructure.getFeature().getProperty().getDescription();
		if ((description != null) && !description.isEmpty()) {
			obfuscatedFeature.getProperty().setDescription(getObfuscatedDescription(description));
		}

		obfuscatedFeatureModel.addFeature(obfuscatedFeature);
		final IFeatureStructure obfuscatedFeatureStructure = obfuscatedFeature.getStructure();
		obfuscatedFeatureStructure.setAbstract(orgFeatureStructure.isAbstract());
		obfuscatedFeatureStructure.setMandatory(orgFeatureStructure.isMandatory());
		obfuscatedFeatureStructure.setAND(orgFeatureStructure.isAnd());
		obfuscatedFeatureStructure.setMultiple(orgFeatureStructure.isMultiple());
		obfuscatedFeatureStructure.setHidden(orgFeatureStructure.isHidden());
		if (parentFeature == null) {
			obfuscatedFeatureModel.getStructure().setRoot(obfuscatedFeatureStructure);
		} else {
			parentFeature.getStructure().addChild(obfuscatedFeatureStructure);
		}

		for (final IFeatureStructure orgChildStructure : orgFeatureStructure.getChildren()) {
			obfuscateStructure(orgChildStructure, obfuscatedFeature);
		}
	}

	protected void obfuscateConstraints() {
		for (final IConstraint constraint : orgFeatureModel.getConstraints()) {
			final Node clone = constraint.getNode().clone();
			for (final Literal literal : clone.getLiterals()) {
				literal.var = getObfuscatedFeatureName(literal.var.toString());
			}
			obfuscatedFeatureModel.addConstraint(factory.createConstraint(obfuscatedFeatureModel, clone));
		}
	}

	protected String getObfuscatedFeatureName(String name) {
		return obfuscate(name, new char[RESULT_LENGTH]);
	}

	protected String getObfuscatedDescription(String description) {
		return obfuscate(description, new char[RESULT_LENGTH]);
	}

	protected String obfuscate(String string, final char[] result) {
		digest.reset();
		digest.update(salt);
		digest.update(string.getBytes(StandardCharsets.UTF_8));
		final byte[] hash = digest.digest();

		return Base32Encoder.encode(result, 0, hash);
	}

	public static String getRandomSalt() {
		final byte[] saltArray = new byte[24];
		secureRandom.nextBytes(saltArray);
		return Base32Encoder.encode(new char[20], 0, saltArray);
	}

}
