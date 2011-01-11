/**
 * <copyright>
 * </copyright>
 *
 * $Id$
 */
package ProjectGeneration.impl;

import ProjectGeneration.ProjectGenerationPackage;
import ProjectGeneration.ProjectSettings;
import ProjectGeneration.SampleSet;

import org.eclipse.emf.common.notify.Notification;

import org.eclipse.emf.ecore.EClass;

import org.eclipse.emf.ecore.impl.ENotificationImpl;
import org.eclipse.emf.ecore.impl.EObjectImpl;

/**
 * <!-- begin-user-doc -->
 * An implementation of the model object '<em><b>Project Settings</b></em>'.
 * <!-- end-user-doc -->
 * <p>
 * The following features are implemented:
 * <ul>
 *   <li>{@link ProjectGeneration.impl.ProjectSettingsImpl#getName <em>Name</em>}</li>
 *   <li>{@link ProjectGeneration.impl.ProjectSettingsImpl#getSampleSet <em>Sample Set</em>}</li>
 * </ul>
 * </p>
 *
 * @generated
 */
public class ProjectSettingsImpl extends EObjectImpl implements ProjectSettings {
	/**
	 * The default value of the '{@link #getName() <em>Name</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getName()
	 * @generated
	 * @ordered
	 */
	protected static final String NAME_EDEFAULT = null;

	/**
	 * The cached value of the '{@link #getName() <em>Name</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getName()
	 * @generated
	 * @ordered
	 */
	protected String name = NAME_EDEFAULT;

	/**
	 * The default value of the '{@link #getSampleSet() <em>Sample Set</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getSampleSet()
	 * @generated
	 * @ordered
	 */
	protected static final SampleSet SAMPLE_SET_EDEFAULT = SampleSet.EMPTY;

	/**
	 * The cached value of the '{@link #getSampleSet() <em>Sample Set</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getSampleSet()
	 * @generated
	 * @ordered
	 */
	protected SampleSet sampleSet = SAMPLE_SET_EDEFAULT;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	protected ProjectSettingsImpl() {
		super();
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	protected EClass eStaticClass() {
		return ProjectGenerationPackage.Literals.PROJECT_SETTINGS;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public String getName() {
		return name;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public void setName(String newName) {
		String oldName = name;
		name = newName;
		if (eNotificationRequired())
			eNotify(new ENotificationImpl(this, Notification.SET, ProjectGenerationPackage.PROJECT_SETTINGS__NAME, oldName, name));
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public SampleSet getSampleSet() {
		return sampleSet;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public void setSampleSet(SampleSet newSampleSet) {
		SampleSet oldSampleSet = sampleSet;
		sampleSet = newSampleSet == null ? SAMPLE_SET_EDEFAULT : newSampleSet;
		if (eNotificationRequired())
			eNotify(new ENotificationImpl(this, Notification.SET, ProjectGenerationPackage.PROJECT_SETTINGS__SAMPLE_SET, oldSampleSet, sampleSet));
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public Object eGet(int featureID, boolean resolve, boolean coreType) {
		switch (featureID) {
			case ProjectGenerationPackage.PROJECT_SETTINGS__NAME:
				return getName();
			case ProjectGenerationPackage.PROJECT_SETTINGS__SAMPLE_SET:
				return getSampleSet();
		}
		return super.eGet(featureID, resolve, coreType);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public void eSet(int featureID, Object newValue) {
		switch (featureID) {
			case ProjectGenerationPackage.PROJECT_SETTINGS__NAME:
				setName((String)newValue);
				return;
			case ProjectGenerationPackage.PROJECT_SETTINGS__SAMPLE_SET:
				setSampleSet((SampleSet)newValue);
				return;
		}
		super.eSet(featureID, newValue);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public void eUnset(int featureID) {
		switch (featureID) {
			case ProjectGenerationPackage.PROJECT_SETTINGS__NAME:
				setName(NAME_EDEFAULT);
				return;
			case ProjectGenerationPackage.PROJECT_SETTINGS__SAMPLE_SET:
				setSampleSet(SAMPLE_SET_EDEFAULT);
				return;
		}
		super.eUnset(featureID);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public boolean eIsSet(int featureID) {
		switch (featureID) {
			case ProjectGenerationPackage.PROJECT_SETTINGS__NAME:
				return NAME_EDEFAULT == null ? name != null : !NAME_EDEFAULT.equals(name);
			case ProjectGenerationPackage.PROJECT_SETTINGS__SAMPLE_SET:
				return sampleSet != SAMPLE_SET_EDEFAULT;
		}
		return super.eIsSet(featureID);
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public String toString() {
		if (eIsProxy()) return super.toString();

		StringBuffer result = new StringBuffer(super.toString());
		result.append(" (name: ");
		result.append(name);
		result.append(", sampleSet: ");
		result.append(sampleSet);
		result.append(')');
		return result.toString();
	}

} //ProjectSettingsImpl
