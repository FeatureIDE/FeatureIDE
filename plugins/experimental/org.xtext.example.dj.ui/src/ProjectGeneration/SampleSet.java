/**
 * <copyright>
 * </copyright>
 *
 * $Id$
 */
package ProjectGeneration;

import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import org.eclipse.emf.common.util.Enumerator;

/**
 * <!-- begin-user-doc -->
 * A representation of the literals of the enumeration '<em><b>Sample Set</b></em>',
 * and utility methods for working with them.
 * <!-- end-user-doc -->
 * @see ProjectGeneration.ProjectGenerationPackage#getSampleSet()
 * @model
 * @generated
 */
public enum SampleSet implements Enumerator {
	/**
	 * The '<em><b>EMPTY</b></em>' literal object.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #EMPTY_VALUE
	 * @generated
	 * @ordered
	 */
	EMPTY(0, "EMPTY", "EMPTY"), /**
	 * The '<em><b>ARTICLE 2005</b></em>' literal object.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #ARTICLE_2005_VALUE
	 * @generated
	 * @ordered
	 */
	ARTICLE_2005(1, "ARTICLE_2005", "ARTICLE_2005")
	, /**
	 * The '<em><b>ACCOUNT SIMPLE CORE</b></em>' literal object.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #ACCOUNT_SIMPLE_CORE_VALUE
	 * @generated
	 * @ordered
	 */
	ACCOUNT_SIMPLE_CORE(2, "ACCOUNT_SIMPLE_CORE", "ACCOUNT_SIMPLE_CORE"), /**
	 * The '<em><b>ACCOUNT COMPLEX CORE</b></em>' literal object.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #ACCOUNT_COMPLEX_CORE_VALUE
	 * @generated
	 * @ordered
	 */
	ACCOUNT_COMPLEX_CORE(3, "ACCOUNT_COMPLEX_CORE", "ACCOUNT_COMPLEX_CORE");

	/**
	 * The '<em><b>EMPTY</b></em>' literal value.
	 * <!-- begin-user-doc -->
	 * <p>
	 * If the meaning of '<em><b>EMPTY</b></em>' literal object isn't clear,
	 * there really should be more of a description here...
	 * </p>
	 * <!-- end-user-doc -->
	 * @see #EMPTY
	 * @model
	 * @generated
	 * @ordered
	 */
	public static final int EMPTY_VALUE = 0;

/**
	 * The '<em><b>ARTICLE 2005</b></em>' literal value.
	 * <!-- begin-user-doc -->
	 * <p>
	 * If the meaning of '<em><b>ARTICLE 2005</b></em>' literal object isn't clear,
	 * there really should be more of a description here...
	 * </p>
	 * <!-- end-user-doc -->
	 * @see #ARTICLE_2005
	 * @model
	 * @generated
	 * @ordered
	 */
	public static final int ARTICLE_2005_VALUE = 1;

	/**
	 * The '<em><b>ACCOUNT SIMPLE CORE</b></em>' literal value.
	 * <!-- begin-user-doc -->
	 * <p>
	 * If the meaning of '<em><b>ACCOUNT SIMPLE CORE</b></em>' literal object isn't clear,
	 * there really should be more of a description here...
	 * </p>
	 * <!-- end-user-doc -->
	 * @see #ACCOUNT_SIMPLE_CORE
	 * @model
	 * @generated
	 * @ordered
	 */
	public static final int ACCOUNT_SIMPLE_CORE_VALUE = 2;

/**
	 * The '<em><b>ACCOUNT COMPLEX CORE</b></em>' literal value.
	 * <!-- begin-user-doc -->
	 * <p>
	 * If the meaning of '<em><b>ACCOUNT COMPLEX CORE</b></em>' literal object isn't clear,
	 * there really should be more of a description here...
	 * </p>
	 * <!-- end-user-doc -->
	 * @see #ACCOUNT_COMPLEX_CORE
	 * @model
	 * @generated
	 * @ordered
	 */
	public static final int ACCOUNT_COMPLEX_CORE_VALUE = 3;

/**
	 * An array of all the '<em><b>Sample Set</b></em>' enumerators.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private static final SampleSet[] VALUES_ARRAY =
		new SampleSet[] {
			EMPTY,
			ARTICLE_2005,
			ACCOUNT_SIMPLE_CORE,
			ACCOUNT_COMPLEX_CORE,
		};

	/**
	 * A public read-only list of all the '<em><b>Sample Set</b></em>' enumerators.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public static final List<SampleSet> VALUES = Collections.unmodifiableList(Arrays.asList(VALUES_ARRAY));

	/**
	 * Returns the '<em><b>Sample Set</b></em>' literal with the specified literal value.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public static SampleSet get(String literal) {
		for (int i = 0; i < VALUES_ARRAY.length; ++i) {
			SampleSet result = VALUES_ARRAY[i];
			if (result.toString().equals(literal)) {
				return result;
			}
		}
		return null;
	}

	/**
	 * Returns the '<em><b>Sample Set</b></em>' literal with the specified name.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public static SampleSet getByName(String name) {
		for (int i = 0; i < VALUES_ARRAY.length; ++i) {
			SampleSet result = VALUES_ARRAY[i];
			if (result.getName().equals(name)) {
				return result;
			}
		}
		return null;
	}

	/**
	 * Returns the '<em><b>Sample Set</b></em>' literal with the specified integer value.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public static SampleSet get(int value) {
		switch (value) {
			case EMPTY_VALUE: return EMPTY;
			case ARTICLE_2005_VALUE: return ARTICLE_2005;
			case ACCOUNT_SIMPLE_CORE_VALUE: return ACCOUNT_SIMPLE_CORE;
			case ACCOUNT_COMPLEX_CORE_VALUE: return ACCOUNT_COMPLEX_CORE;
		}
		return null;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private final int value;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private final String name;

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private final String literal;

	/**
	 * Only this class can construct instances.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	private SampleSet(int value, String name, String literal) {
		this.value = value;
		this.name = name;
		this.literal = literal;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	public int getValue() {
	  return value;
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
	public String getLiteral() {
	  return literal;
	}

	/**
	 * Returns the literal value of the enumerator, which is its string representation.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public String toString() {
		return literal;
	}
	
} //SampleSet
